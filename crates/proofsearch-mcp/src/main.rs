use std::path::PathBuf;
use std::sync::Arc;
use tokio::sync::Mutex;
use tokio::io::{stdin, stdout};
use rusqlite::Connection;
use clap::Parser;

use rmcp::service::serve_server;
use rmcp::transport::async_rw::AsyncRwTransport;

use proofsearch_mcp::{init_db, ChatDbMcp};

/// LLM-Driven Proof Search Environment MCP Server — Verifier-backed RL environment for LLM-driven proof search
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

    /// Database path (also settable via PROOFSEARCH_DB_PATH env var)
    #[arg(default_value = "proofsearch.db")]
    db_path: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    let db_path = std::env::var("PROOFSEARCH_DB_PATH")
        .unwrap_or(cli.db_path);

    let conn = Connection::open(&db_path)?;
    conn.execute_batch("
        PRAGMA journal_mode = WAL;
        PRAGMA busy_timeout = 5000;
        PRAGMA foreign_keys = ON;
    ")?;

    init_db(&conn)?;

    let home = std::env::var("USERPROFILE")
        .or_else(|_| std::env::var("HOME"))
        .unwrap_or_else(|_| "C:\\Users\\mnehm".to_string());

    let lean_project_path = std::env::var("PROOFSEARCH_LEAN_PROJECT_PATH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| std::env::current_dir().unwrap().join("lean-checker"));
    let elan_bin_path = std::env::var("PROOFSEARCH_ELAN_BIN_PATH")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(home).join(".elan").join("bin"));

    let shared_conn = Arc::new(Mutex::new(conn));
    let shared_lean_project = lean_project_path.clone();
    let shared_elan_bin = elan_bin_path.clone();

    match cli.transport.as_str() {
        "stdio" => {
            let handler = ChatDbMcp::new(shared_conn, lean_project_path, elan_bin_path);
            if !handler.lean_available {
                eprintln!(
                    "WARNING: Lean gateway unavailable (looked for lakefile under {:?} and lake.exe under {:?}). \
                     'solve' actions will fail with an infrastructure error until lean-checker/ is set up — see README.",
                    shared_lean_project, shared_elan_bin
                );
            }

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
                    Ok(ChatDbMcp::new(conn_for_factory.clone(), lean_for_factory.clone(), elan_for_factory.clone()))
                },
                LocalSessionManager::default().into(),
                Default::default(),
            );

            let app = axum::Router::new()
                .nest_service("/mcp", service);

            let bind_addr = format!("{}:{}", cli.host, cli.port);
            eprintln!("LLM-Driven Proof Search Environment MCP HTTP server listening on http://{}/mcp", bind_addr);
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
