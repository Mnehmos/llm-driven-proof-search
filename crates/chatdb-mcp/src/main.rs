use std::path::PathBuf;
use std::sync::Arc;
use tokio::sync::Mutex;
use tokio::io::{stdin, stdout};
use rusqlite::{Connection, OptionalExtension};
use uuid::Uuid;
use chrono::Utc;
use serde::{Deserialize, Serialize};
use schemars::JsonSchema;
use clap::Parser;

use rmcp::ServerHandler;
use rmcp::model::*;
use rmcp::service::{serve_server, RequestContext, RoleServer};
use rmcp::transport::async_rw::AsyncRwTransport;
use rmcp::ErrorData as McpError;

use chatdb_proof_core::db::schema_v1;
use chatdb_proof_core::orchestrator::{lifecycle, step, trajectories};
use chatdb_proof_core::lean::RealLeanGateway;
use chatdb_proof_core::models::action::{TypedAction, ActionRequest, ActionRole, StepDisposition};
use chatdb_proof_core::models::episode::{EpisodeOutcome, TerminationReason, TruncationReason};
use chatdb_proof_core::models::reward::{RewardComponent, RewardComponentId, RewardPolicy};

/// ChatDB MCP Server — Verifier-backed RL environment for LLM-driven proof search
#[derive(Parser, Debug)]
#[command(version, about)]
struct Cli {
    /// Transport mode: stdio (default) or http
    #[arg(long, default_value = "stdio")]
    transport: String,

    /// Port for HTTP transport (only used when --transport http)
    #[arg(long, default_value = "8080")]
    port: u16,

    /// Bind address for HTTP transport
    #[arg(long, default_value = "127.0.0.1")]
    host: String,

    /// Database path (also settable via CHATDB_DB_PATH env var)
    #[arg(default_value = "chatdb.db")]
    db_path: String,
}


// Define arg structs for schemars and serde
#[derive(JsonSchema, Deserialize)]
struct EnvironmentDescribeArgs {}

#[derive(JsonSchema, Deserialize)]
struct EpisodeCreateArgs {
    problem_version_id: String,
    #[serde(default)]
    max_steps: Option<i32>,
    #[serde(default)]
    cost_budget_micros: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
struct EpisodeResetArgs {
    episode_id: String,
}

#[derive(JsonSchema, Deserialize)]
struct EpisodeObserveArgs {
    episode_id: String,
}

#[derive(JsonSchema, Deserialize)]
struct EpisodeStepArgs {
    episode_id: String,
    action_attempt_id: String,
    expected_revision: i64,
    claim_token: String,
    action: TypedAction,
    cost_micros: i64,
}

#[derive(JsonSchema, Deserialize)]
struct EpisodeStatusArgs {
    episode_id: String,
}

#[derive(JsonSchema, Deserialize)]
struct EpisodeCloseArgs {
    episode_id: String,
    reason: String,
}

#[derive(JsonSchema, Deserialize)]
struct ModelCallReserveArgs {
    episode_id: String,
    action_attempt_id: String,
    runner_id: String,
    declared_model: String,
    max_input_tokens: i64,
    max_output_tokens: i64,
    reserved_cost_micros: i64,
}

#[derive(JsonSchema, Deserialize)]
struct ModelCallSettleArgs {
    lease_id: String,
    actual_cost_micros: i64,
    status: String,
}

#[derive(JsonSchema, Deserialize)]
struct TrajectoryExportArgs {
    episode_id: String,
    #[serde(default)]
    cursor: Option<i64>,
    #[serde(default)]
    page_size: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
struct EpisodeReplayArgs {
    episode_id: String,
}

fn make_tool<T: JsonSchema>(name: &'static str, desc: &'static str) -> Tool {
    let settings = schemars::r#gen::SchemaSettings::draft07().with(|s| {
        s.option_nullable = true;
        s.option_add_null_type = false;
    });
    let generator = settings.into_generator();
    let mut schema = generator.into_root_schema_for::<T>();
    schema.schema.metadata().id = Some("https://json-schema.org/draft/2020-12/schema".to_string());
    let val = serde_json::to_value(schema.schema).unwrap();
    let obj = val.as_object().unwrap().clone();
    Tool::new(name, desc, obj)
}

fn query_action_request(conn: &Connection, id: Uuid) -> Result<ActionRequest, rusqlite::Error> {
    conn.query_row(
        "SELECT id, episode_id, problem_version_id, episode_revision, request_sequence_number, role, state_hash_before, status, expiration_at, created_at FROM action_requests WHERE id = ?1",
        [id.to_string()],
        |row| {
            let id_str: String = row.get(0)?;
            let ep_id_str: String = row.get(1)?;
            let pv_id_str: String = row.get(2)?;
            let role_str: String = row.get(5)?;
            let role = match role_str.as_str() {
                "prover" => ActionRole::Prover,
                "reviewer" => ActionRole::Reviewer,
                _ => ActionRole::Human,
            };
            let created_at_str: String = row.get(9)?;
            let created_at = chrono::DateTime::parse_from_rfc3339(&created_at_str).unwrap().with_timezone(&Utc);
            let exp_str: Option<String> = row.get(8)?;
            let expiration_at = exp_str.map(|s| chrono::DateTime::parse_from_rfc3339(&s).unwrap().with_timezone(&Utc));

            Ok(ActionRequest {
                id: Uuid::parse_str(&id_str).unwrap(),
                episode_id: Uuid::parse_str(&ep_id_str).unwrap(),
                problem_version_id: Uuid::parse_str(&pv_id_str).unwrap(),
                episode_revision: row.get(3)?,
                request_sequence_number: row.get(4)?,
                role,
                state_hash_before: row.get(6)?,
                status: row.get(7)?,
                expiration_at,
                created_at,
            })
        }
    )
}

fn mcp_invalid_params(msg: impl Into<std::borrow::Cow<'static, str>>) -> McpError {
    McpError::new(ErrorCode::INVALID_PARAMS, msg, None)
}

fn mcp_internal_error(msg: impl Into<std::borrow::Cow<'static, str>>) -> McpError {
    McpError::new(ErrorCode::INTERNAL_ERROR, msg, None)
}

struct ChatDbMcp {
    conn: Arc<Mutex<Connection>>,
    gateway: RealLeanGateway,
}

impl ServerHandler for ChatDbMcp {
    fn get_info(&self) -> ServerInfo {
        ServerInfo::new(ServerCapabilities::default())
            .with_server_info(Implementation::new("chatdb-mcp", "0.1.0"))
    }

    async fn list_tools(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListToolsResult, McpError> {
        let tools = vec![
            make_tool::<EnvironmentDescribeArgs>("environment_describe", "Return environment version, supported protocol, tool schemas, capabilities"),
            make_tool::<EpisodeCreateArgs>("episode_create", "Initialize an episode from a problem version + config. Returns first observation"),
            make_tool::<EpisodeResetArgs>("episode_reset", "Nondestructive: creates new episode from existing config, sets parent_episode_id"),
            make_tool::<EpisodeObserveArgs>("episode_observe", "Get the active observation and pending action request"),
            make_tool::<EpisodeStepArgs>("episode_step", "Submit typed action with revision + idempotency key. Settles lease atomically if provided"),
            make_tool::<EpisodeStatusArgs>("episode_status", "Retrieve current episode state, revision, budget, step count"),
            make_tool::<EpisodeCloseArgs>("episode_close", "Gracefully truncate an episode"),
            make_tool::<ModelCallReserveArgs>("model_call_reserve", "Reserve a budget lease for a model call"),
            make_tool::<ModelCallSettleArgs>("model_call_settle", "Settle or release a lease without submitting an action (provider failure, cancellation)"),
            make_tool::<TrajectoryExportArgs>("trajectory_export", "Export trajectory with pagination (cursor + page_size)"),
            make_tool::<EpisodeReplayArgs>("episode_replay", "Re-execute typed actions through canonical reducer with Lean re-verification"),
        ];
        Ok(ListToolsResult::with_all_items(tools))
    }

    async fn call_tool(
        &self,
        request: CallToolRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> Result<CallToolResult, McpError> {
        let args_map = request.arguments.unwrap_or_default();
        let args_val = serde_json::Value::Object(args_map);

        match request.name.as_ref() {
            "environment_describe" => {
                let res = serde_json::json!({
                    "environment_version": "0.1.0",
                    "protocol_version": "2025-11-25",
                    "supported_roles": ["prover"],
                    "schema_versions": {
                        "observation_schema_version": "1.0",
                        "action_schema_version": "1.0",
                        "reward_policy_version": "1.0"
                    }
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "episode_create" => {
                let args: EpisodeCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                
                let problem_uuid = Uuid::parse_str(&args.problem_version_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid problem Uuid: {}", e)))?;
                
                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(|e| mcp_internal_error(e.to_string()))?;
                
                let episode_uuid = lifecycle::episode_create(&tx, problem_uuid)
                    .map_err(|e| mcp_internal_error(e.to_string()))?;
                
                if let Some(ms) = args.max_steps {
                    tx.execute("UPDATE episodes SET max_steps = ?1 WHERE id = ?2", (ms, episode_uuid.to_string()))
                        .map_err(|e| mcp_internal_error(e.to_string()))?;
                }
                if let Some(cb) = args.cost_budget_micros {
                    tx.execute("UPDATE episodes SET cost_budget_micros = ?1 WHERE id = ?2", (cb, episode_uuid.to_string()))
                        .map_err(|e| mcp_internal_error(e.to_string()))?;
                }

                let next_req_id = lifecycle::advance(&tx, episode_uuid)
                    .map_err(|e| mcp_internal_error(e.to_string()))?;
                
                tx.commit().map_err(|e| mcp_internal_error(e.to_string()))?;

                let (state,): (String,) = conn.query_row(
                    "SELECT state FROM episodes WHERE id = ?1",
                    [episode_uuid.to_string()],
                    |row| Ok((row.get(0)?,)),
                ).map_err(|e| mcp_internal_error(e.to_string()))?;

                let next_action_request = if let Some(req_id) = next_req_id {
                    Some(query_action_request(&conn, req_id).map_err(|e| mcp_internal_error(e.to_string()))?)
                } else {
                    None
                };

                let res = serde_json::json!({
                    "episode_id": episode_uuid.to_string(),
                    "state": state,
                    "next_action_request": next_action_request
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "episode_reset" => {
                let args: EpisodeResetArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                
                let old_ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;
                
                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(|e| mcp_internal_error(e.to_string()))?;
                
                let new_ep_uuid = lifecycle::episode_reset(&tx, old_ep_uuid)
                    .map_err(|e| mcp_internal_error(e.to_string()))?;
                
                let next_req_id = lifecycle::advance(&tx, new_ep_uuid)
                    .map_err(|e| mcp_internal_error(e.to_string()))?;
                
                tx.commit().map_err(|e| mcp_internal_error(e.to_string()))?;

                let (state,): (String,) = conn.query_row(
                    "SELECT state FROM episodes WHERE id = ?1",
                    [new_ep_uuid.to_string()],
                    |row| Ok((row.get(0)?,)),
                ).map_err(|e| mcp_internal_error(e.to_string()))?;

                let next_action_request = if let Some(req_id) = next_req_id {
                    Some(query_action_request(&conn, req_id).map_err(|e| mcp_internal_error(e.to_string()))?)
                } else {
                    None
                };

                let res = serde_json::json!({
                    "episode_id": new_ep_uuid.to_string(),
                    "state": state,
                    "next_action_request": next_action_request
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "episode_observe" => {
                let args: EpisodeObserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                
                let conn = self.conn.lock().await;
                
                let active_req_id_str: Option<String> = conn.query_row(
                    "SELECT id FROM action_requests WHERE episode_id = ?1 AND status IN ('pending', 'claimed') ORDER BY created_at DESC LIMIT 1",
                    [args.episode_id.clone()],
                    |row| row.get(0),
                ).optional().map_err(|e| mcp_internal_error(e.to_string()))?;

                if let Some(req_id_str) = active_req_id_str {
                    let req_id = Uuid::parse_str(&req_id_str).unwrap();
                    let action_request = query_action_request(&conn, req_id)
                        .map_err(|e| mcp_internal_error(e.to_string()))?;
                    
                    let obs_json: Option<String> = conn.query_row(
                        "SELECT observation_json FROM action_requests WHERE id = ?1",
                        [req_id_str],
                        |row| row.get(0),
                    ).map_err(|e| mcp_internal_error(e.to_string()))?;
                    
                    let observation = obs_json.and_then(|s| serde_json::from_str(&s).ok()).unwrap_or(serde_json::Value::Null);

                    let res = serde_json::json!({
                        "action_request": action_request,
                        "observation": observation
                    });
                    Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
                } else {
                    Err(mcp_invalid_params("No active request found"))
                }
            }
            "episode_step" => {
                let args: EpisodeStepArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                
                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;
                
                let attempt_uuid = Uuid::parse_str(&args.action_attempt_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid attempt Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(|e| mcp_internal_error(e.to_string()))?;

                // Deduct or settle leases if any exist
                tx.execute(
                    "UPDATE model_call_leases SET status = 'settled', actual_cost_micros = ?1, settled_at = ?2 
                     WHERE episode_id = ?3 AND action_attempt_id = ?4 AND status = 'reserved'",
                    (args.cost_micros, Utc::now().to_rfc3339(), args.episode_id.clone(), args.action_attempt_id.clone()),
                ).map_err(|e| mcp_internal_error(e.to_string()))?;

                let outcome_res = step::attempt_commit(
                    &tx,
                    attempt_uuid,
                    args.expected_revision,
                    &args.claim_token,
                    &args.action,
                    &self.gateway,
                    args.cost_micros as i128,
                );

                let (disposition, accepted, error_msg) = match outcome_res {
                    Ok(chatdb_proof_core::models::LeanVerificationOutcome::KernelPass) => {
                        (StepDisposition::Accepted, true, None)
                    }
                    Ok(_) => {
                        (StepDisposition::Accepted, false, None)
                    }
                    Err(step::StepError::Conflict) => {
                        (StepDisposition::StaleRevision, false, Some("Revision conflict".to_string()))
                    }
                    Err(step::StepError::InvalidAttempt) => {
                        (StepDisposition::InvalidResponse, false, Some("Invalid attempt claim or status".to_string()))
                    }
                    Err(e) => {
                        (StepDisposition::Error, false, Some(format!("{:?}", e)))
                    }
                };

                let mut is_terminated = false;
                let mut is_truncated = false;
                let mut term_reason = None;
                let mut trunc_reason = None;
                let mut outcome_enum = None;

                if disposition == StepDisposition::Accepted {
                    // Check if root is proved
                    let root_status: String = tx.query_row(
                        "SELECT status FROM episode_obligations WHERE episode_id = ?1 AND kind = 'root'",
                        [args.episode_id.clone()],
                        |row| row.get(0),
                    ).map_err(|e| mcp_internal_error(e.to_string()))?;

                    if root_status == "proved" {
                        tx.execute(
                            "UPDATE episodes SET state = 'terminated', outcome = 'terminated', termination_reason = 'root_proved', completed_at = ?1 WHERE id = ?2",
                            (Utc::now().to_rfc3339(), args.episode_id.clone()),
                        ).map_err(|e| mcp_internal_error(e.to_string()))?;
                        is_terminated = true;
                        term_reason = Some(TerminationReason::RootProved);
                        outcome_enum = Some(EpisodeOutcome::Terminated);
                    } else {
                        // Check step limit
                        let (steps, max_steps): (i64, Option<i64>) = tx.query_row(
                            "SELECT step_count, max_steps FROM episodes WHERE id = ?1",
                            [args.episode_id.clone()],
                            |row| Ok((row.get(0)?, row.get(1)?)),
                        ).map_err(|e| mcp_internal_error(e.to_string()))?;

                        if let Some(max) = max_steps {
                            if steps >= max {
                                tx.execute(
                                    "UPDATE episodes SET state = 'truncated', outcome = 'truncated', truncation_reason = 'budget_exhausted', completed_at = ?1 WHERE id = ?2",
                                    (Utc::now().to_rfc3339(), args.episode_id.clone()),
                                ).map_err(|e| mcp_internal_error(e.to_string()))?;
                                is_truncated = true;
                                trunc_reason = Some(TruncationReason::BudgetExhausted);
                                outcome_enum = Some(EpisodeOutcome::Truncated);
                            }
                        }
                    }
                }

                // If not ended, call advance to prepare the next request
                let next_req_id = if !is_terminated && !is_truncated && disposition == StepDisposition::Accepted {
                    lifecycle::advance(&tx, ep_uuid)
                        .map_err(|e| mcp_internal_error(e.to_string()))?
                } else {
                    None
                };

                tx.commit().map_err(|e| mcp_internal_error(e.to_string()))?;

                // Calculate reward
                let mut reward_components = Vec::new();
                let policy = RewardPolicy::default_policy();
                reward_components.push(RewardComponent {
                    id: RewardComponentId::StepPenalty,
                    value_scaled: policy.step_penalty,
                });
                if disposition == StepDisposition::Accepted {
                    if accepted {
                        reward_components.push(RewardComponent {
                            id: RewardComponentId::KernelPass,
                            value_scaled: policy.kernel_pass,
                        });
                    } else {
                        reward_components.push(RewardComponent {
                            id: RewardComponentId::KernelFail,
                            value_scaled: policy.kernel_fail,
                        });
                    }
                }
                if is_terminated {
                    reward_components.push(RewardComponent {
                        id: RewardComponentId::TerminalSuccess,
                        value_scaled: policy.terminal_success,
                    });
                } else if is_truncated {
                    reward_components.push(RewardComponent {
                        id: RewardComponentId::TruncationPenalty,
                        value_scaled: policy.truncation_penalty,
                    });
                }

                let next_action_request = if let Some(req_id) = next_req_id {
                    Some(query_action_request(&conn, req_id).map_err(|e| mcp_internal_error(e.to_string()))?)
                } else {
                    None
                };

                let observation = if let Some(ref req) = next_action_request {
                    let obs_json: Option<String> = conn.query_row(
                        "SELECT observation_json FROM action_requests WHERE id = ?1",
                        [req.id.to_string()],
                        |row| row.get(0),
                    ).optional().map_err(|e| mcp_internal_error(e.to_string()))?.flatten();
                    obs_json.and_then(|s| serde_json::from_str(&s).ok()).unwrap_or(serde_json::Value::Null)
                } else {
                    serde_json::Value::Null
                };

                let res = serde_json::json!({
                    "accepted": accepted,
                    "disposition": disposition,
                    "counts_as_environment_step": disposition == StepDisposition::Accepted,
                    "reward": reward_components,
                    "outcome": outcome_enum,
                    "termination_reason": term_reason,
                    "truncation_reason": trunc_reason,
                    "diagnostics": error_msg,
                    "next_action_request": next_action_request,
                    "observation": observation
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "episode_status" => {
                let args: EpisodeStatusArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                
                let conn = self.conn.lock().await;
                let status = conn.query_row(
                    "SELECT state, current_revision, step_count, cost_budget_micros, invalid_action_count, termination_reason, truncation_reason 
                     FROM episodes WHERE id = ?1",
                    [args.episode_id.clone()],
                    |row| {
                        Ok(serde_json::json!({
                            "state": row.get::<_, String>(0)?,
                            "current_revision": row.get::<_, i64>(1)?,
                            "step_count": row.get::<_, i64>(2)?,
                            "cost_budget_micros": row.get::<_, i64>(3)?,
                            "invalid_action_count": row.get::<_, i64>(4)?,
                            "termination_reason": row.get::<_, Option<String>>(5)?,
                            "truncation_reason": row.get::<_, Option<String>>(6)?,
                        }))
                    }
                ).map_err(|e| mcp_internal_error(e.to_string()))?;

                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&status).unwrap())]))
            }
            "episode_close" => {
                let args: EpisodeCloseArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                
                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(|e| mcp_internal_error(e.to_string()))?;
                
                tx.execute(
                    "UPDATE episodes SET state = 'truncated', outcome = 'truncated', truncation_reason = 'human_cancelled', completed_at = ?1 WHERE id = ?2",
                    (Utc::now().to_rfc3339(), args.episode_id.clone()),
                ).map_err(|e| mcp_internal_error(e.to_string()))?;
                
                tx.commit().map_err(|e| mcp_internal_error(e.to_string()))?;
                
                let res = serde_json::json!({ "status": "closed" });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "model_call_reserve" => {
                let args: ModelCallReserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                
                let lease_id = Uuid::new_v4();
                let descriptor = serde_json::json!({
                    "runner_id": args.runner_id,
                    "declared_model": args.declared_model,
                    "max_input_tokens": args.max_input_tokens,
                    "max_output_tokens": args.max_output_tokens,
                });
                let descriptor_json = serde_json::to_string(&descriptor).unwrap();

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(|e| mcp_internal_error(e.to_string()))?;
                
                tx.execute(
                    "INSERT INTO model_call_leases (
                        id, episode_id, action_attempt_id, model_descriptor_json, reserved_cost_micros, status, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, 'reserved', ?6)",
                    (
                        lease_id.to_string(),
                        args.episode_id.clone(),
                        args.action_attempt_id.clone(),
                        descriptor_json,
                        args.reserved_cost_micros,
                        Utc::now().to_rfc3339(),
                    ),
                ).map_err(|e| mcp_internal_error(e.to_string()))?;
                
                tx.commit().map_err(|e| mcp_internal_error(e.to_string()))?;

                let res = serde_json::json!({ "lease_id": lease_id.to_string() });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "model_call_settle" => {
                let args: ModelCallSettleArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                
                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(|e| mcp_internal_error(e.to_string()))?;

                tx.execute(
                    "UPDATE model_call_leases SET status = ?1, actual_cost_micros = ?2, settled_at = ?3 WHERE id = ?4",
                    (args.status.clone(), args.actual_cost_micros, Utc::now().to_rfc3339(), args.lease_id.clone()),
                ).map_err(|e| mcp_internal_error(e.to_string()))?;

                let episode_id: String = tx.query_row(
                    "SELECT episode_id FROM model_call_leases WHERE id = ?1",
                    [args.lease_id.clone()],
                    |row| row.get(0),
                ).map_err(|e| mcp_internal_error(e.to_string()))?;

                tx.execute(
                    "UPDATE episodes SET cost_budget_micros = cost_budget_micros - ?1 WHERE id = ?2",
                    (args.actual_cost_micros, episode_id),
                ).map_err(|e| mcp_internal_error(e.to_string()))?;

                tx.commit().map_err(|e| mcp_internal_error(e.to_string()))?;

                let res = serde_json::json!({ "status": "settled" });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "trajectory_export" => {
                let args: TrajectoryExportArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                
                let page_size = args.page_size.unwrap_or(50);
                let cursor = args.cursor.unwrap_or(0);

                let conn = self.conn.lock().await;
                let mut stmt = conn.prepare(
                    "SELECT id, event_sequence_number, event_type, event_hash, previous_event_hash, 
                            state_hash_before, state_hash_after, lean_environment_hash, payload_json, created_at 
                     FROM trajectory_events 
                     WHERE episode_id = ?1 AND event_sequence_number >= ?2 
                     ORDER BY event_sequence_number ASC LIMIT ?3"
                ).map_err(|e| mcp_internal_error(e.to_string()))?;

                let rows = stmt.query_map((args.episode_id.clone(), cursor, page_size), |row| {
                    Ok(serde_json::json!({
                        "id": row.get::<_, i64>(0)?,
                        "event_sequence_number": row.get::<_, i64>(1)?,
                        "event_type": row.get::<_, String>(2)?,
                        "event_hash": row.get::<_, String>(3)?,
                        "previous_event_hash": row.get::<_, String>(4)?,
                        "state_hash_before": row.get::<_, String>(5)?,
                        "state_hash_after": row.get::<_, String>(6)?,
                        "lean_environment_hash": row.get::<_, String>(7)?,
                        "payload": serde_json::from_str::<serde_json::Value>(&row.get::<_, String>(8)?).unwrap_or(serde_json::Value::Null),
                        "created_at": row.get::<_, String>(9)?,
                    }))
                }).map_err(|e| mcp_internal_error(e.to_string()))?
                .collect::<Result<Vec<_>, _>>()
                .map_err(|e| mcp_internal_error(e.to_string()))?;

                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&rows).unwrap())]))
            }
            "episode_replay" => {
                let args: EpisodeReplayArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                
                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;

                let conn = self.conn.lock().await;
                let audit_ok = trajectories::audit_trajectory(&conn, ep_uuid)
                    .map_err(|e| mcp_internal_error(e.to_string()))?;

                let replay_ok = trajectories::replay_trajectory(&conn, ep_uuid, &self.gateway)
                    .map_err(|e| mcp_internal_error(e.to_string()))?;

                let res = serde_json::json!({
                    "audit_passed": audit_ok,
                    "replay_status": format!("{:?}", replay_ok)
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            _ => Err(McpError::new(ErrorCode::METHOD_NOT_FOUND, format!("Method not found: {}", request.name), None)),
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    
    let db_path = std::env::var("CHATDB_DB_PATH")
        .unwrap_or(cli.db_path);

    let conn = Connection::open(&db_path)?;
    conn.execute("PRAGMA journal_mode = WAL;", [])?;
    conn.execute("PRAGMA busy_timeout = 5000;", [])?;
    conn.execute("PRAGMA foreign_keys = ON;", [])?;
    
    schema_v1::initialize_v1_db(&conn)?;

    let home = std::env::var("USERPROFILE")
        .or_else(|_| std::env::var("HOME"))
        .unwrap_or_else(|_| "C:\\Users\\mnehm".to_string());
    
    let lean_project_path = std::env::var("CHATDB_LEAN_PROJECT_PATH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| std::env::current_dir().unwrap().join("lean-checker"));
    let elan_bin_path = std::env::var("CHATDB_ELAN_BIN_PATH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(home).join(".elan").join("bin"));

    let shared_conn = Arc::new(Mutex::new(conn));
    let shared_lean_project = lean_project_path.clone();
    let shared_elan_bin = elan_bin_path.clone();

    match cli.transport.as_str() {
        "stdio" => {
            let gateway = RealLeanGateway::new(lean_project_path, elan_bin_path);
            let handler = ChatDbMcp {
                conn: shared_conn,
                gateway,
            };

            let transport = AsyncRwTransport::new(stdin(), stdout());
            let service = serve_server(handler, transport).await?;
            service.waiting().await?;
        }
        "http" => {
            use rmcp::transport::streamable_http_server::{
                StreamableHttpService,
                session::local::LocalSessionManager,
            };

            let conn_for_factory = shared_conn.clone();
            let lean_for_factory = shared_lean_project.clone();
            let elan_for_factory = shared_elan_bin.clone();

            let service = StreamableHttpService::new(
                move || {
                    let gateway = RealLeanGateway::new(
                        lean_for_factory.clone(),
                        elan_for_factory.clone(),
                    );
                    Ok(ChatDbMcp {
                        conn: conn_for_factory.clone(),
                        gateway,
                    })
                },
                LocalSessionManager::default().into(),
                Default::default(),
            );

            let app = axum::Router::new()
                .nest_service("/mcp", service);

            let bind_addr = format!("{}:{}", cli.host, cli.port);
            eprintln!("ChatDB MCP HTTP server listening on http://{}/mcp", bind_addr);
            let listener = tokio::net::TcpListener::bind(&bind_addr).await?;
            axum::serve(listener, app).await?;
        }
        other => {
            eprintln!("Unknown transport: {}. Use 'stdio' or 'http'.", other);
            std::process::exit(1);
        }
    }

    Ok(())

}

#[cfg(test)]
mod tests {
    use super::*;
    use rmcp::service::serve_client;
    use rmcp::model::{CallToolRequestParams, ClientInfo};
    use std::borrow::Cow;

    #[tokio::test]
    async fn test_mcp_list_tools_and_describe() {
        let conn = Connection::open_in_memory().unwrap();
        schema_v1::initialize_v1_db(&conn).unwrap();
        
        let lean_project_path = PathBuf::from("dummy_path");
        let elan_bin_path = PathBuf::from("dummy_path");
        let gateway = RealLeanGateway::new(lean_project_path, elan_bin_path);
        
        let handler = ChatDbMcp {
            conn: Arc::new(Mutex::new(conn)),
            gateway,
        };

        // Create tokio duplex channels
        let (client_stream, server_stream) = tokio::io::duplex(2048);
        let (client_read, client_write) = tokio::io::split(client_stream);
        let (server_read, server_write) = tokio::io::split(server_stream);

        let server_transport = AsyncRwTransport::new(server_read, server_write);
        let client_transport = AsyncRwTransport::new(client_read, client_write);

        // Serve server in background task
        tokio::spawn(async move {
            if let Ok(service) = serve_server(handler, server_transport).await {
                let _ = service.waiting().await;
            }
        });

        // Serve client
        let client_info = Implementation::new("test-client", "1.0.0");
        let capabilities = ClientCapabilities::default();
        let service = InitializeRequestParams::new(capabilities, client_info);
        let client_service = serve_client(service, client_transport).await.unwrap();
        let client_peer = client_service.peer();

        // 1. Verify list_tools
        let list_res = client_peer.list_tools(None).await.unwrap();
        assert_eq!(list_res.tools.len(), 11);

        // 2. Verify environment_describe
        let call_params = CallToolRequestParams::new("environment_describe");
        let call_res = client_peer.call_tool(call_params).await.unwrap();
        assert!(!call_res.is_error.unwrap_or(false));
        let text_content = call_res.content[0].as_text().unwrap();
        assert!(text_content.text.contains("2025-11-25"));
    }
}
