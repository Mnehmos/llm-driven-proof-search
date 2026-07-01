use rusqlite::Connection;
use std::fs;
use std::path::Path;

use chatdb_proof_core::db;

#[test]
fn test_dump_v0_schema_baseline() -> rusqlite::Result<()> {
    let conn = Connection::open_in_memory()?;
    db::initialize_db(&conn)?;

    let mut stmt = conn.prepare("SELECT type, name, sql FROM sqlite_master WHERE sql IS NOT NULL ORDER BY type DESC, name ASC")?;
    let mut rows = stmt.query([])?;

    let mut schema_dump = String::new();
    while let Some(row) = rows.next()? {
        let type_str: String = row.get(0)?;
        let name_str: String = row.get(1)?;
        let sql_str: String = row.get(2)?;
        schema_dump.push_str(&format!("-- {} {}\n{};\n\n", type_str, name_str, sql_str));
    }

    let fixture_path = Path::new("fixtures/v0_baseline_schema.sql");
    fs::create_dir_all("fixtures").unwrap();
    fs::write(fixture_path, schema_dump).expect("Failed to write fixture");
    
    Ok(())
}
