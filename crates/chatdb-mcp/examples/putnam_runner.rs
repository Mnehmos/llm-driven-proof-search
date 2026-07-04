//! PutnamBench pass@k runner (issue #31).
//!
//! Drives already-imported (see `import_putnambench`, issue #29)
//! `benchmark_problems` rows through the REAL, tracked proof-search loop —
//! `episode_create` -> `attempt_claim` -> `episode_step` — and records
//! results via `benchmark_result_record`. Per issue #36's invariant, this
//! runner NEVER calls `RealLeanGateway`/`LeanGateway::verify_exact` /
//! `verify_module` directly: every candidate attempt is measured only if it
//! actually went through `episode_step`.
//!
//! This runner does not generate candidate proofs itself — ChatDB has no
//! embedded model (see `readme_first`: the model/agent lives outside
//! ChatDB). Candidate attempts come from an "attempts plan" JSON file
//! supplied by whatever produced them (a human, an external agent, or a
//! fixed canned set for smoke-testing):
//!
//! ```json
//! {
//!   "problems": [
//!     { "upstream_problem_id": "putnam_1962_a1", "attempts": [
//!       { "proof_term": "..." }
//!     ]},
//!     { "upstream_problem_id": "putnam_1962_a5", "attempts": [
//!       { "answer_value": "fun n => n * (n + 1) * 2 ^ (n - 2)", "proof_term": "..." }
//!     ]}
//!   ]
//! }
//! ```
//!
//! `answer_value` is required exactly for problems with a solution abbrev
//! (`chatdb_proof_core::putnambench::to_pi_form`'s `solution_abbrev`) — those
//! are submitted as `SubmitModule` (the abbrev as a `def` module item plus
//! the root theorem); everything else is a bare `Solve`. Attempts for one
//! problem are tried in order, up to `attempt_budget`, stopping at the first
//! kernel_verified/certified result — `pass_at` is the 1-based index of the
//! attempt that succeeded.
//!
//! Usage:
//!   cargo run --release --example putnam_runner -- <db_path> <attempts_plan.json> <solve_mode> <attempt_budget> [result_output.jsonl]
//!   solve_mode: solve_only | submit_module_allowed

use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;
use std::sync::Arc;
use tokio::sync::Mutex;
use rusqlite::Connection;

use rmcp::model::{CallToolRequestParams, ClientCapabilities, Implementation, InitializeRequestParams};
use rmcp::service::{serve_client, serve_server};
use rmcp::transport::async_rw::AsyncRwTransport;

use chatdb_mcp::{init_db, ChatDbMcp};
use chatdb_proof_core::putnambench::to_pi_form;

#[derive(serde::Deserialize)]
struct AttemptsPlan {
    problems: Vec<PlannedProblem>,
}

#[derive(serde::Deserialize)]
struct PlannedProblem {
    upstream_problem_id: String,
    attempts: Vec<PlannedAttempt>,
}

#[derive(serde::Deserialize)]
struct PlannedAttempt {
    #[serde(default)]
    answer_value: Option<String>,
    proof_term: String,
}

struct ResultRow {
    upstream_problem_id: String,
    status: String,
    pass_at: Option<usize>,
    attempts_used: usize,
}

/// Maps a concluded episode's real recorded `outcome` onto
/// `benchmark_results.status`'s vocabulary — never invented independently of
/// what the ledger actually recorded (issue #36).
fn status_for_outcome(outcome: &str) -> &'static str {
    match outcome {
        "certified" => "certified",
        "kernel_verified" => "kernel_verified",
        "timeout" => "timeout",
        "model_error" | "infrastructure_error" => "infra_error",
        // refuted, gave_up, budget_exhausted: a definitive non-success within
        // budget, distinct from an infra/tooling failure.
        _ => "failed",
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 5 {
        eprintln!("usage: putnam_runner <db_path> <attempts_plan.json> <solve_only|submit_module_allowed> <attempt_budget> [result_output.jsonl]");
        std::process::exit(1);
    }
    let db_path = &args[1];
    let plan_path = &args[2];
    let solve_mode_str = args[3].as_str();
    let attempt_budget: i64 = args[4].parse()?;
    let output_path = args.get(5).cloned();
    if !matches!(solve_mode_str, "solve_only" | "submit_module_allowed") {
        eprintln!("solve_mode must be 'solve_only' or 'submit_module_allowed', got {:?}", solve_mode_str);
        std::process::exit(1);
    }

    let plan: AttemptsPlan = serde_json::from_str(&std::fs::read_to_string(plan_path)?)?;
    let plan_by_id: HashMap<String, &PlannedProblem> = plan.problems.iter().map(|p| (p.upstream_problem_id.clone(), p)).collect();

    let conn = Connection::open(db_path)?;
    conn.execute_batch("PRAGMA journal_mode = WAL; PRAGMA busy_timeout = 5000; PRAGMA foreign_keys = ON;")?;
    init_db(&conn)?;

    let suite_id: String = conn.query_row(
        "SELECT id FROM benchmark_suites WHERE name = 'PutnamBench'", [], |row| row.get(0),
    ).map_err(|_| "no 'PutnamBench' benchmark suite in this db — run import_putnambench first")?;

    // For each planned problem, read its catalog row directly (no MCP tool
    // exists to fetch a single benchmark_problems row by upstream id; this is
    // a plain read of already-imported, non-sensitive catalog data).
    struct CatalogRow {
        benchmark_problem_id: String,
        theorem_name: String,
        root_formal_statement: String,
        /// The exact text to submit to problem_create — the catalog's own
        /// prover_ready_statement when the importer registered one (so this
        /// is BYTE-IDENTICAL to what benchmark_result_record's cross-check
        /// will hash-compare against), otherwise a freshly-computed
        /// to_pi_form fallback.
        submit_statement: String,
        import_manifest_json: String,
    }
    let mut catalog: HashMap<String, CatalogRow> = HashMap::new();
    for upstream_id in plan_by_id.keys() {
        let row: Option<(String, String, String, Option<String>, String)> = conn.query_row(
            "SELECT id, theorem_name, root_formal_statement, prover_ready_statement, import_manifest_json
             FROM benchmark_problems WHERE suite_id = ?1 AND upstream_problem_id = ?2",
            (&suite_id, upstream_id),
            |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?, r.get(4)?)),
        ).ok();
        if let Some((id, name, stmt, prover_ready, manifest)) = row {
            let submit_statement = match prover_ready {
                Some(s) => s,
                None => match to_pi_form(&stmt, &name) {
                    Ok(form) => form.root_theorem_statement,
                    Err(e) => {
                        eprintln!("WARNING: '{}' has no stored prover_ready_statement and to_pi_form fallback failed ({}) — skipping", upstream_id, e);
                        continue;
                    }
                },
            };
            catalog.insert(upstream_id.clone(), CatalogRow { benchmark_problem_id: id, theorem_name: name, root_formal_statement: stmt, submit_statement, import_manifest_json: manifest });
        } else {
            eprintln!("WARNING: planned problem '{}' not found in benchmark_problems for suite PutnamBench — skipping", upstream_id);
        }
    }

    let lean_project_path = std::env::var("CHATDB_LEAN_PROJECT_PATH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| std::env::current_dir().unwrap().join("lean-checker"));
    let elan_bin_path = std::env::var("CHATDB_ELAN_BIN_PATH")
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
    let client_info = Implementation::new("putnam-runner-client", "1.0.0");
    let init = InitializeRequestParams::new(ClientCapabilities::default(), client_info);
    let client = serve_client(init, client_transport).await?;
    let peer = client.peer();

    async fn call(peer: &rmcp::service::Peer<rmcp::RoleClient>, tool: &str, args: serde_json::Value) -> Result<serde_json::Value, String> {
        let res = peer.call_tool(CallToolRequestParams::new(tool.to_string()).with_arguments(args.as_object().cloned().unwrap_or_default())).await
            .map_err(|e| format!("transport error calling {}: {:?}", tool, e))?;
        let text = res.content.first().and_then(|c| c.as_text()).map(|t| t.text.clone()).unwrap_or_default();
        if res.is_error.unwrap_or(false) {
            return Err(format!("{} failed: {}", tool, text));
        }
        serde_json::from_str(&text).map_err(|e| format!("{} returned non-JSON: {} ({})", tool, text, e))
    }

    let run_res = call(&peer, "benchmark_run_create", serde_json::json!({
        "suite_id": suite_id, "solve_mode": solve_mode_str, "attempt_budget": attempt_budget,
    })).await?;
    let run_id = run_res["run_id"].as_str().unwrap().to_string();
    eprintln!("Created run {} (solve_mode={}, attempt_budget={})", run_id, solve_mode_str, attempt_budget);

    let mut results: Vec<ResultRow> = Vec::new();

    for planned in &plan.problems {
        let Some(cat) = catalog.get(&planned.upstream_problem_id) else { continue };

        let form = match to_pi_form(&cat.root_formal_statement, &cat.theorem_name) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("FORMALIZATION GAP {}: could not convert to Pi-form: {}", planned.upstream_problem_id, e);
                call(&peer, "benchmark_result_record", serde_json::json!({
                    "run_id": run_id, "benchmark_problem_id": cat.benchmark_problem_id,
                    "status": "formalization_gap", "attempts_used": 0,
                })).await.ok();
                results.push(ResultRow { upstream_problem_id: planned.upstream_problem_id.clone(), status: "formalization_gap".to_string(), pass_at: None, attempts_used: 0 });
                continue;
            }
        };

        if solve_mode_str == "solve_only" && form.solution_abbrev.is_some() {
            eprintln!("SKIPPED {}: needs SubmitModule (has a solution abbrev), run is solve_only", planned.upstream_problem_id);
            call(&peer, "benchmark_result_record", serde_json::json!({
                "run_id": run_id, "benchmark_problem_id": cat.benchmark_problem_id,
                "status": "skipped", "attempts_used": 0,
            })).await.ok();
            results.push(ResultRow { upstream_problem_id: planned.upstream_problem_id.clone(), status: "skipped".to_string(), pass_at: None, attempts_used: 0 });
            continue;
        }

        let import_manifest: Vec<String> = serde_json::from_str(&cat.import_manifest_json).unwrap_or_default();
        let pv_res = match call(&peer, "problem_create", serde_json::json!({
            "source_problem_text": format!("PutnamBench {}", planned.upstream_problem_id),
            "root_formal_statement": cat.submit_statement,
            "problem_imports": import_manifest,
            "unsafe_dev_attestation": true,
        })).await {
            Ok(r) => r,
            Err(e) => {
                eprintln!("INFRA ERROR {}: problem_create failed: {}", planned.upstream_problem_id, e);
                call(&peer, "benchmark_result_record", serde_json::json!({
                    "run_id": run_id, "benchmark_problem_id": cat.benchmark_problem_id,
                    "status": "infra_error", "attempts_used": 0,
                })).await.ok();
                results.push(ResultRow { upstream_problem_id: planned.upstream_problem_id.clone(), status: "infra_error".to_string(), pass_at: None, attempts_used: 0 });
                continue;
            }
        };
        let pv_id = pv_res["problem_version_id"].as_str().unwrap().to_string();

        let ep_res = call(&peer, "episode_create", serde_json::json!({
            "problem_version_id": pv_id, "max_steps": attempt_budget + 1,
        })).await?;
        let episode_id = ep_res["episode_id"].as_str().unwrap().to_string();
        let mut next_request = ep_res["next_action_request"].clone();

        let mut final_outcome: Option<String> = None;
        let mut pass_at: Option<usize> = None;
        let mut attempts_used = 0usize;

        for (i, attempt) in planned.attempts.iter().enumerate().take(attempt_budget as usize) {
            if next_request.is_null() {
                break;
            }

            // Checked BEFORE claiming: a real bug an adversarial review
            // found had this check AFTER attempt_claim, so a skipped
            // attempt left the action_request stuck in 'claimed' state —
            // the NEXT attempt_claim call (on the same still-outstanding
            // request) then failed outright, and that error's `?` crashed
            // the entire runner process, abandoning every other queued
            // problem. Checking first means a missing answer_value just
            // moves on to the next planned attempt with the request still
            // claimable.
            let action = if let Some(abbrev) = &form.solution_abbrev {
                let Some(answer_value) = &attempt.answer_value else {
                    eprintln!("SKIPPING attempt {} for {}: needs answer_value (has a solution abbrev) but none was given", i + 1, planned.upstream_problem_id);
                    continue;
                };
                serde_json::json!({
                    "type": "submit_module",
                    "module_items": [{"item_kind": "def", "name": abbrev.name, "type_signature": abbrev.type_signature, "body": answer_value}],
                    // Must be BYTE-IDENTICAL to what problem_create received
                    // (cat.submit_statement) — SubmitModule's root_theorem.statement
                    // must canonical-hash to the problem's registered
                    // root_statement_hash, and using form.root_theorem_statement
                    // here (a fresh to_pi_form re-derivation) would only
                    // coincidentally match if the importer's own
                    // prover_ready_statement was never used.
                    "root_theorem": {"name": "root", "statement": cat.submit_statement, "proof_term": attempt.proof_term},
                })
            } else {
                serde_json::json!({"type": "solve", "proof_term": attempt.proof_term})
            };

            let claim = call(&peer, "attempt_claim", serde_json::json!({
                "episode_id": episode_id, "action_request_id": next_request["id"],
                "idempotency_key": format!("{}-attempt-{}", planned.upstream_problem_id, i + 1),
                "expected_revision": next_request["episode_revision"],
            })).await?;

            let step = call(&peer, "episode_step", serde_json::json!({
                "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
                "expected_revision": next_request["episode_revision"], "claim_token": claim["claim_token"],
                "action": action, "cost_micros": 1,
            })).await?;
            attempts_used = i + 1;

            if let Some(outcome) = step["outcome"].as_str() {
                final_outcome = Some(outcome.to_string());
                if matches!(outcome, "kernel_verified" | "certified") {
                    pass_at = Some(i + 1);
                }
                break;
            }
            next_request = step["next_action_request"].clone();
        }

        // Every episode this runner touches must reach a definitive outcome
        // before benchmark_result_record can reference it (issue #36's
        // "unconcluded episode" check) — if the plan ran out of attempts
        // (or had none) without the episode itself terminating, close it out
        // honestly with GiveUp rather than leaving it dangling open.
        if final_outcome.is_none() && !next_request.is_null() {
            let claim = call(&peer, "attempt_claim", serde_json::json!({
                "episode_id": episode_id, "action_request_id": next_request["id"],
                "idempotency_key": format!("{}-giveup", planned.upstream_problem_id),
                "expected_revision": next_request["episode_revision"],
            })).await?;
            let step = call(&peer, "episode_step", serde_json::json!({
                "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
                "expected_revision": next_request["episode_revision"], "claim_token": claim["claim_token"],
                "action": {"type": "give_up"}, "cost_micros": 1,
            })).await?;
            final_outcome = step["outcome"].as_str().map(|s| s.to_string());
        }

        let status = final_outcome.as_deref().map(status_for_outcome).unwrap_or("infra_error").to_string();
        call(&peer, "benchmark_result_record", serde_json::json!({
            "run_id": run_id, "benchmark_problem_id": cat.benchmark_problem_id,
            "problem_version_id": pv_id, "episode_id": episode_id,
            "status": status, "pass_at": pass_at, "attempts_used": attempts_used.max(1),
        })).await?;

        eprintln!("{}: status={} pass_at={:?} attempts_used={}", planned.upstream_problem_id, status, pass_at, attempts_used);
        results.push(ResultRow { upstream_problem_id: planned.upstream_problem_id.clone(), status, pass_at, attempts_used });
    }

    let observed = call(&peer, "benchmark_run_observe", serde_json::json!({"run_id": run_id})).await?;

    let mut jsonl = String::new();
    for r in &results {
        jsonl.push_str(&serde_json::to_string(&serde_json::json!({
            "upstream_problem_id": r.upstream_problem_id, "status": r.status,
            "pass_at": r.pass_at, "attempts_used": r.attempts_used,
        })).unwrap());
        jsonl.push('\n');
    }
    if let Some(path) = &output_path {
        std::fs::write(path, &jsonl)?;
        eprintln!("Wrote {} result rows to {}", results.len(), path);
    } else {
        print!("{}", jsonl);
    }

    eprintln!("\n=== putnam_runner summary ===");
    eprintln!("run_id: {}", run_id);
    eprintln!("{}", serde_json::to_string_pretty(&observed["metrics"]).unwrap());
    eprintln!("| upstream_problem_id | status | pass_at | attempts_used |");
    eprintln!("|---|---|---|---|");
    for r in &results {
        eprintln!("| {} | {} | {} | {} |", r.upstream_problem_id, r.status,
            r.pass_at.map(|p| p.to_string()).unwrap_or_else(|| "-".to_string()), r.attempts_used);
    }

    let _ = std::io::stdout().flush();
    Ok(())
}
