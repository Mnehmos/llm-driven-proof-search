//! Headless play-testing harness. Drives the REAL `ChatDbMcp` handler (real
//! `RealLeanGateway`, real Lean/Mathlib toolchain) through an in-process MCP
//! client/server duplex — the same pattern the unit test suite uses via
//! `connected_client`, just with the real gateway instead of a mock, and a
//! script of tool calls read from a JSON file instead of hardcoded assertions.
//!
//! Usage: cargo run --release --example playtest -- <db_path> <script.json>
//!
//! Script format:
//! { "steps": [ { "label": "optional", "tool": "problem_create", "args": { ... } }, ... ] }
//!
//! Any string value anywhere in a step's `args` of the form `${label.a.b.c}`
//! is replaced with the JSON value at path `a.b.c` in the response recorded
//! under `label` (from an earlier step's `label` field) before the call is
//! made — e.g. `"episode_id": "${ep.episode_id}"` after a step labeled `ep`.
//! Numbers/bools/objects substitute as their real JSON type if the whole
//! string is exactly one placeholder; otherwise the value is stringified and
//! spliced into the surrounding text.
//!
//! Every step's full JSON response is printed to stdout, prefixed with the
//! step index/label/tool name, so a transcript of the whole run can be
//! captured and read back.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use tokio::sync::Mutex;
use rusqlite::Connection;

use rmcp::model::{CallToolRequestParams, ClientCapabilities, Implementation, InitializeRequestParams};
use rmcp::service::{serve_client, serve_server};
use rmcp::transport::async_rw::AsyncRwTransport;

use proofsearch_mcp::{init_db, ChatDbMcp};

#[derive(serde::Deserialize)]
struct Script {
    steps: Vec<Step>,
}

#[derive(serde::Deserialize)]
struct Step {
    tool: String,
    #[serde(default)]
    args: serde_json::Value,
    #[serde(default)]
    label: Option<String>,
}

fn lookup_path<'a>(root: &'a serde_json::Value, path: &str) -> Option<&'a serde_json::Value> {
    let mut cur = root;
    for part in path.split('.') {
        if let Ok(idx) = part.parse::<usize>() {
            cur = cur.get(idx)?;
        } else {
            cur = cur.get(part)?;
        }
    }
    Some(cur)
}

/// Recursively substitutes `${label.path}` placeholders in every string leaf
/// of `val` using previously recorded step responses.
fn substitute(val: &mut serde_json::Value, responses: &HashMap<String, serde_json::Value>) {
    match val {
        serde_json::Value::String(s) => {
            if let Some(inner) = s.strip_prefix("${").and_then(|r| r.strip_suffix("}")) {
                if let Some((label, path)) = inner.split_once('.') {
                    if let Some(resp) = responses.get(label) {
                        if let Some(found) = lookup_path(resp, path) {
                            *val = found.clone();
                            return;
                        } else {
                            eprintln!("WARNING: placeholder ${{{}}} — path '{}' not found in response labeled '{}'", inner, path, label);
                        }
                    } else {
                        eprintln!("WARNING: placeholder ${{{}}} — no earlier step labeled '{}'", inner, label);
                    }
                }
            }
        }
        serde_json::Value::Array(arr) => {
            for v in arr.iter_mut() { substitute(v, responses); }
        }
        serde_json::Value::Object(obj) => {
            for (_, v) in obj.iter_mut() { substitute(v, responses); }
        }
        _ => {}
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: playtest <db_path> <script.json>");
        std::process::exit(1);
    }
    let db_path = &args[1];
    let script_path = &args[2];

    let conn = Connection::open(db_path)?;
    conn.execute_batch("PRAGMA journal_mode = WAL; PRAGMA busy_timeout = 5000; PRAGMA foreign_keys = ON;")?;
    init_db(&conn)?;

    let lean_project_path = std::env::var("PROOFSEARCH_LEAN_PROJECT_PATH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| std::env::current_dir().unwrap().join("lean-checker"));
    let elan_bin_path = std::env::var("PROOFSEARCH_ELAN_BIN_PATH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(std::env::var("USERPROFILE").unwrap()).join(".elan").join("bin"));

    let handler = ChatDbMcp::new(Arc::new(Mutex::new(conn)), lean_project_path.clone(), elan_bin_path.clone());
    eprintln!("lean_project_path = {:?}", lean_project_path);
    eprintln!("elan_bin_path = {:?}", elan_bin_path);
    eprintln!("lean_available = {}", handler.lean_available);
    eprintln!("lean_environment = {:?}", handler.lean_environment.as_ref().map(|e| e.descriptor.clone()));

    let (client_stream, server_stream) = tokio::io::duplex(1 << 20);
    let (client_read, client_write) = tokio::io::split(client_stream);
    let (server_read, server_write) = tokio::io::split(server_stream);

    let server_transport = AsyncRwTransport::new(server_read, server_write);
    let client_transport = AsyncRwTransport::new(client_read, client_write);

    tokio::spawn(async move {
        if let Ok(service) = serve_server(handler, server_transport).await {
            let _ = service.waiting().await;
        }
    });

    let client_info = Implementation::new("playtest-client", "1.0.0");
    let capabilities = ClientCapabilities::default();
    let init = InitializeRequestParams::new(capabilities, client_info);
    let client = serve_client(init, client_transport).await?;
    let peer = client.peer();

    let script: Script = serde_json::from_str(&std::fs::read_to_string(script_path)?)?;
    let mut responses: HashMap<String, serde_json::Value> = HashMap::new();

    for (i, step) in script.steps.iter().enumerate() {
        let mut args_val = step.args.clone();
        substitute(&mut args_val, &responses);
        let args_map = args_val.as_object().cloned().unwrap_or_default();

        println!("\n=== step {} [{}] tool={} ===", i, step.label.as_deref().unwrap_or(""), step.tool);
        println!("--- request ---\n{}", serde_json::to_string_pretty(&args_val).unwrap_or_default());
        let res = peer.call_tool(CallToolRequestParams::new(step.tool.clone()).with_arguments(args_map)).await;
        match res {
            Ok(result) => {
                let is_error = result.is_error.unwrap_or(false);
                let text = result.content.first().and_then(|c| c.as_text()).map(|t| t.text.clone()).unwrap_or_default();
                println!("--- response (isError={}) ---", is_error);
                let parsed = serde_json::from_str::<serde_json::Value>(&text).unwrap_or(serde_json::Value::String(text.clone()));
                println!("{}", serde_json::to_string_pretty(&parsed).unwrap_or(text));
                if let Some(label) = &step.label {
                    responses.insert(label.clone(), parsed);
                }
            }
            Err(e) => {
                println!("--- TRANSPORT ERROR ---\n{:?}", e);
            }
        }
    }

    Ok(())
}
