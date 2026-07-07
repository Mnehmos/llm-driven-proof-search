//! One-time/batch importer for PutnamBench (https://github.com/trishullab/PutnamBench)
//! Lean 4 problems into LLM-Driven Proof Search Environment's benchmark_* schema (issue #29).
//!
//! PutnamBench is never fetched or vendored by this repo — clone it yourself
//! and point this tool at that local clone, mirroring the
//! PROOFSEARCH_LEAN_PROJECT_PATH/lean-checker convention already used for the Lean
//! toolchain itself:
//!
//!   git clone https://github.com/trishullab/PutnamBench.git /some/local/path
//!   cargo run --release --example import_putnambench -- <db_path> /some/local/path [problem_name ...]
//!
//! With no problem names given, every `lean4/src/*.lean` file is imported.
//! With one or more names given (e.g. for issue #32's smoke subset), only
//! those problems are imported.
//!
//! Extraction mirrors PutnamBench's own `lean4/scripts/extract_to_json.py`:
//! every file is `import Mathlib` followed by an optional `open ...` line, an
//! optional docstring, an optional `abbrev`/`noncomputable abbrev
//! <name>_solution : <type> := sorry` declaration (roughly half of
//! PutnamBench's problems ask the prover to state an answer, not just supply
//! a bare proof — those need `SubmitModule`, not `Solve`, since the
//! abbrev's real body must be supplied alongside the theorem's proof), and
//! exactly one `theorem <name> ... := sorry` (confirmed against the full
//! 672-file corpus: zero files have more than one `theorem` declaration).
//! `root_formal_statement` is registered as the abbrev-if-present-plus-theorem
//! text, faithfully matching what PutnamBench itself extracts as
//! `lean4_statement` — a runner (issue #31) is responsible for splitting the
//! abbrev out into a `SubmitModule` module_item when one is present (detect
//! by checking whether the stored statement contains "abbrev" before
//! "theorem").
//!
//! The informal (natural-language) problem statement and subject tags come
//! from `informal/putnam.json`, keyed by `problem_name`, and are logged but
//! not currently stored (benchmark_problems has no tags/informal-statement
//! column — `source_problem_text` belongs to problem_versions, a different,
//! per-episode record created later by an actual solve attempt, not to the
//! benchmark_problems catalog entry itself).
//!
//! Files that don't match the expected shape are skipped and reported on
//! stderr with a reason — never silently mis-registered.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use tokio::sync::Mutex;
use rusqlite::Connection;

use rmcp::model::{CallToolRequestParams, ClientCapabilities, Implementation, InitializeRequestParams};
use rmcp::service::{serve_client, serve_server};
use rmcp::transport::async_rw::AsyncRwTransport;

use proofsearch_mcp::{init_db, ChatDbMcp};
use proofsearch_core::putnambench::{parse_problem_file, to_pi_form, ParsedProblem};

#[derive(serde::Deserialize)]
struct InformalEntry {
    problem_name: String,
    #[serde(default)]
    tags: Vec<String>,
}

fn git_head_commit(repo_path: &Path) -> Option<String> {
    std::process::Command::new("git")
        .args(["-C", repo_path.to_str()?, "rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: import_putnambench <db_path> <putnambench_repo_path> [problem_name ...]");
        std::process::exit(1);
    }
    let db_path = &args[1];
    let repo_path = PathBuf::from(&args[2]);
    let only_names: Option<std::collections::HashSet<String>> = if args.len() > 3 {
        Some(args[3..].iter().cloned().collect())
    } else {
        None
    };

    let src_dir = repo_path.join("lean4").join("src");
    let informal_path = repo_path.join("informal").join("putnam.json");
    if !src_dir.is_dir() {
        eprintln!("ERROR: {:?} is not a directory — is --repo-path a real PutnamBench clone?", src_dir);
        std::process::exit(1);
    }

    let informal: HashMap<String, InformalEntry> = if informal_path.exists() {
        let raw = std::fs::read_to_string(&informal_path)?;
        let entries: Vec<InformalEntry> = serde_json::from_str(&raw)?;
        entries.into_iter().map(|e| (e.problem_name.clone(), e)).collect()
    } else {
        eprintln!("WARNING: {:?} not found — proceeding without informal statements/tags", informal_path);
        HashMap::new()
    };

    let mut parsed: Vec<(String, ParsedProblem)> = Vec::new();
    let mut skipped: Vec<(String, String)> = Vec::new();
    let mut entries: Vec<_> = std::fs::read_dir(&src_dir)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(|e| e.path());
    for entry in entries {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("lean") {
            continue;
        }
        let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("").to_string();
        if let Some(names) = &only_names {
            if !names.contains(&stem) {
                continue;
            }
        }
        let text = match std::fs::read_to_string(&path) {
            Ok(t) => t,
            Err(e) => { skipped.push((stem, format!("read error: {}", e))); continue; }
        };
        match parse_problem_file(&text) {
            Ok(p) => parsed.push((stem, p)),
            Err(reason) => skipped.push((stem, reason)),
        }
    }

    if let Some(names) = &only_names {
        let found: std::collections::HashSet<&String> = parsed.iter().map(|(s, _)| s).collect();
        for wanted in names {
            if !found.contains(wanted) && !skipped.iter().any(|(s, _)| s == wanted) {
                eprintln!("WARNING: requested problem '{}' was not found in {:?}", wanted, src_dir);
            }
        }
    }

    eprintln!("Parsed {} problems, skipped {} files.", parsed.len(), skipped.len());
    for (stem, reason) in &skipped {
        eprintln!("  SKIPPED {}: {}", stem, reason);
    }
    if !informal.is_empty() {
        let missing_informal: Vec<&String> = parsed.iter().map(|(s, _)| s).filter(|s| !informal.contains_key(*s)).collect();
        eprintln!(
            "{}/{} parsed problems have a matching informal/putnam.json entry (e.g. tags: {:?} for the first match).",
            parsed.len() - missing_informal.len(), parsed.len(),
            parsed.iter().find_map(|(s, _)| informal.get(s)).map(|e| &e.tags),
        );
        if !missing_informal.is_empty() {
            eprintln!("  no informal entry for: {:?}", missing_informal);
        }
    }

    let upstream_commit = git_head_commit(&repo_path);
    eprintln!("PutnamBench upstream_commit = {:?}", upstream_commit);

    let conn = Connection::open(db_path)?;
    conn.execute_batch("PRAGMA journal_mode = WAL; PRAGMA busy_timeout = 5000; PRAGMA foreign_keys = ON;")?;
    init_db(&conn)?;

    // Resumability: benchmark_suites.name is UNIQUE, so a straight
    // benchmark_suite_create on every run would fail outright on any re-run
    // against the same db (e.g. after a crash partway through a 672-problem
    // batch) with no way to recover the existing suite_id through any
    // current MCP tool. Look it up directly on the raw connection instead,
    // before it's moved into the handler, and only create it if truly
    // absent — this makes the importer naturally idempotent/resumable.
    let existing_suite_id: Option<String> = conn.query_row(
        "SELECT id FROM benchmark_suites WHERE name = 'PutnamBench'", [], |row| row.get(0),
    ).ok();

    let lean_project_path = std::env::var("PROOFSEARCH_LEAN_PROJECT_PATH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| std::env::current_dir().unwrap().join("lean-checker"));
    let elan_bin_path = std::env::var("PROOFSEARCH_ELAN_BIN_PATH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(std::env::var("USERPROFILE").unwrap()).join(".elan").join("bin"));
    let handler = ChatDbMcp::new(Arc::new(Mutex::new(conn)), lean_project_path, elan_bin_path);

    let (client_stream, server_stream) = tokio::io::duplex(1 << 22);
    let (client_read, client_write) = tokio::io::split(client_stream);
    let (server_read, server_write) = tokio::io::split(server_stream);
    let server_transport = AsyncRwTransport::new(server_read, server_write);
    let client_transport = AsyncRwTransport::new(client_read, client_write);
    tokio::spawn(async move {
        if let Ok(service) = serve_server(handler, server_transport).await {
            let _ = service.waiting().await;
        }
    });
    let client_info = Implementation::new("import-putnambench-client", "1.0.0");
    let init = InitializeRequestParams::new(ClientCapabilities::default(), client_info);
    let client = serve_client(init, client_transport).await?;
    let peer = client.peer();

    let suite_id = if let Some(id) = existing_suite_id {
        eprintln!("Reusing existing suite PutnamBench (id={}) — resuming a prior import", id);
        id
    } else {
        let suite_args = serde_json::json!({
            "name": "PutnamBench",
            "upstream_url": "https://github.com/trishullab/PutnamBench",
            "upstream_commit": upstream_commit,
            "language": "Lean4",
        });
        let suite_res = peer.call_tool(CallToolRequestParams::new("benchmark_suite_create")
            .with_arguments(suite_args.as_object().unwrap().clone())).await?;
        if suite_res.is_error.unwrap_or(false) {
            let text = suite_res.content.first().and_then(|c| c.as_text()).map(|t| t.text.clone()).unwrap_or_default();
            eprintln!("ERROR creating suite: {}", text);
            std::process::exit(1);
        }
        let suite_json: serde_json::Value = serde_json::from_str(
            &suite_res.content.first().and_then(|c| c.as_text()).map(|t| t.text.clone()).unwrap_or_default()
        )?;
        let id = suite_json["suite_id"].as_str().unwrap().to_string();
        eprintln!("Created suite PutnamBench (id={})", id);
        id
    };

    let mut registered = 0usize;
    let mut register_failed: Vec<(String, String)> = Vec::new();
    let mut solution_abbrev_count = 0usize;
    let mut pi_form_failed: Vec<(String, String)> = Vec::new();
    for (stem, p) in &parsed {
        if p.has_solution_abbrev {
            solution_abbrev_count += 1;
        }
        // benchmark_problem_register derives prover_ready_statement itself
        // (via the same to_pi_form) — this pre-check exists purely to
        // report, at import time, which problems a runner won't be able to
        // attempt at all (root_formal_statement isn't a `theorem NAME
        // (binders) : type` declaration to_pi_form can convert). See
        // migrate_add_prover_ready_statement_columns.
        if let Err(e) = to_pi_form(&p.root_formal_statement, &p.name) {
            pi_form_failed.push((stem.clone(), e));
        }
        let args = serde_json::json!({
            "suite_id": suite_id,
            "upstream_problem_id": stem,
            "theorem_name": p.name,
            "source_file_path": format!("lean4/src/{}.lean", stem),
            "root_formal_statement": p.root_formal_statement,
            "import_manifest": ["Mathlib"],
        });
        let res = peer.call_tool(CallToolRequestParams::new("benchmark_problem_register")
            .with_arguments(args.as_object().unwrap().clone())).await?;
        if res.is_error.unwrap_or(false) {
            let text = res.content.first().and_then(|c| c.as_text()).map(|t| t.text.clone()).unwrap_or_default();
            register_failed.push((stem.clone(), text));
        } else {
            registered += 1;
        }
    }

    eprintln!("\n=== import_putnambench summary ===");
    eprintln!("suite_id: {}", suite_id);
    eprintln!("registered: {}", registered);
    eprintln!("parse-skipped: {}", skipped.len());
    eprintln!("register-failed: {}", register_failed.len());
    eprintln!("pi-form-conversion-failed (registered without prover_ready_statement): {}", pi_form_failed.len());
    eprintln!("problems with a solution abbrev (need SubmitModule, not bare Solve): {}", solution_abbrev_count);
    for (stem, err) in &register_failed {
        eprintln!("  REGISTER FAILED {}: {}", stem, err);
    }
    for (stem, err) in &pi_form_failed {
        eprintln!("  PI-FORM CONVERSION FAILED {}: {} (registered anyway, but a runner cannot attempt this problem until fixed)", stem, err);
    }

    Ok(())
}
