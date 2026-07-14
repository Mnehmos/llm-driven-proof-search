//! Issue #224: server-side ordering of a dependency-closed Lean module.
//!
//! Rather than a client resubmitting every step source through MCP, the server
//! traverses the *verified* obligation graph for an episode (the
//! `episode_obligation_edges` DAG, where every node must carry a positive
//! `episode_verified_lemmas` row), topologically sorts the declarations
//! (dependencies before dependents), and checks interface/environment
//! consistency — producing a validated, deterministic ordering the MCP
//! `module` tool feeds into the existing `assemble_module` + `verify_module`
//! kernel path.
//!
//! This module owns only the *deterministic* graph/order/validation logic —
//! pure given the recorded graph. Proof-source resolution, module rendering,
//! kernel verification, `#print axioms`, and persistence are layered on by the
//! caller, because those reuse the proven SubmitModule assembly path and the
//! live Lean gateway. Keeping ordering deterministic and kernel-free is what
//! makes it unit-testable and replayable.

use rusqlite::{Connection, OptionalExtension};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use uuid::Uuid;

/// A single verified declaration participating in the closure, before ordering.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ClosureNode {
    obligation_id: String,
    theorem_name: String,
    lean_statement: String,
    statement_hash: String,
    environment_hash: String,
    /// Direct dependency obligation IDs restricted to the closure.
    dependency_obligation_ids: Vec<String>,
}

/// A topologically ordered, validated declaration in the closure. The caller
/// resolves the proof body (from the winning attempt / verified module) and maps
/// this to a `LeanModuleItem` / root `ModuleTheorem`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrderedDeclaration {
    pub obligation_id: String,
    pub theorem_name: String,
    pub lean_statement: String,
    pub statement_hash: String,
    /// True for the closure's root theorem (always ordered last).
    pub is_root: bool,
    /// Names of this declaration's direct dependencies (all ordered earlier).
    pub dependency_theorem_names: Vec<String>,
}

/// A manifest entry — everything persistence/replay needs. Hashed (canonically)
/// into `declaration_manifest_hash`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclarationManifestEntry {
    pub order: usize,
    pub theorem_name: String,
    pub statement_hash: String,
    pub is_root: bool,
    pub dependency_theorem_names: Vec<String>,
}

/// A validated, topologically ordered dependency closure ready for assembly.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrderedClosure {
    pub root_obligation_id: String,
    pub root_theorem_name: String,
    pub root_statement_hash: String,
    /// The single pinned environment every declaration shares.
    pub environment_hash: String,
    /// Topologically ordered declarations (dependencies strictly before
    /// dependents; the root is last).
    pub declarations: Vec<OrderedDeclaration>,
    /// Ordered manifest (name/hash/deps), stable across source rendering.
    pub declaration_manifest: Vec<DeclarationManifestEntry>,
    /// Canonical hash over `declaration_manifest` — deterministic per graph.
    pub declaration_manifest_hash: String,
}

/// Structured graph errors — a caller (and its client) can act on the exact
/// failure mode rather than parsing a string.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "error", rename_all = "snake_case")]
pub enum ClosureError {
    /// The requested root obligation does not exist in this episode.
    RootNotFound { obligation_id: String },
    /// A closure node (possibly the root) has no positive verified lemma.
    UnverifiedDependency {
        obligation_id: String,
        theorem_name: Option<String>,
    },
    /// The dependency graph contains a cycle (reported as an ordered name path,
    /// first == last).
    Cycle { cycle_theorem_names: Vec<String> },
    /// Two declarations share a theorem name (a duplicate definition, or the same
    /// name at two statement hashes) — Lean would reject the combined module.
    IncompatibleInterface {
        theorem_name: String,
        statement_hash_a: String,
        statement_hash_b: String,
    },
    /// A declaration was verified under a different pinned environment.
    EnvironmentMismatch {
        theorem_name: String,
        expected_environment_hash: String,
        found_environment_hash: String,
    },
    /// A database error while traversing the graph.
    GraphQueryFailed { detail: String },
}

impl std::fmt::Display for ClosureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClosureError::RootNotFound { obligation_id } => {
                write!(f, "root obligation {obligation_id} not found in this episode")
            }
            ClosureError::UnverifiedDependency { obligation_id, theorem_name } => write!(
                f,
                "dependency {} ({}) has no positive verified lemma",
                obligation_id,
                theorem_name.as_deref().unwrap_or("unknown")
            ),
            ClosureError::Cycle { cycle_theorem_names } => {
                write!(f, "dependency cycle: {}", cycle_theorem_names.join(" -> "))
            }
            ClosureError::IncompatibleInterface { theorem_name, statement_hash_a, statement_hash_b } => write!(
                f,
                "incompatible interface for {theorem_name}: {statement_hash_a} vs {statement_hash_b}"
            ),
            ClosureError::EnvironmentMismatch { theorem_name, expected_environment_hash, found_environment_hash } => write!(
                f,
                "environment mismatch for {theorem_name}: expected {expected_environment_hash}, found {found_environment_hash}"
            ),
            ClosureError::GraphQueryFailed { detail } => write!(f, "graph query failed: {detail}"),
        }
    }
}

fn db_err(e: rusqlite::Error) -> ClosureError {
    ClosureError::GraphQueryFailed {
        detail: e.to_string(),
    }
}

/// Traverse, validate, and topologically order the dependency-closed set of
/// verified declarations rooted at `root_obligation_id` in `episode_id`.
///
/// Deterministic for the same graph: ordering breaks ties by theorem name, so
/// identical graphs always produce identical `declaration_manifest_hash`.
pub fn order_closure(
    conn: &Connection,
    episode_id: Uuid,
    root_obligation_id: Uuid,
) -> Result<OrderedClosure, ClosureError> {
    let nodes = gather_closure(conn, episode_id, root_obligation_id)?;
    check_interfaces(&nodes)?;
    check_environment(&nodes)?;
    let ordered = topological_order(&nodes)?;

    let root_id = root_obligation_id.to_string();
    let root = nodes
        .iter()
        .find(|n| n.obligation_id == root_id)
        .expect("root is always in the gathered closure");
    let root_theorem_name = root.theorem_name.clone();
    let root_statement_hash = root.statement_hash.clone();
    let environment_hash = root.environment_hash.clone();

    let name_of: HashMap<&str, &str> = nodes
        .iter()
        .map(|n| (n.obligation_id.as_str(), n.theorem_name.as_str()))
        .collect();

    let mut declarations = Vec::with_capacity(ordered.len());
    let mut manifest = Vec::with_capacity(ordered.len());
    for (order, node) in ordered.iter().enumerate() {
        let mut dep_names: Vec<String> = node
            .dependency_obligation_ids
            .iter()
            .filter_map(|id| name_of.get(id.as_str()).map(|s| s.to_string()))
            .collect();
        dep_names.sort();
        let is_root = node.obligation_id == root_id;

        declarations.push(OrderedDeclaration {
            obligation_id: node.obligation_id.clone(),
            theorem_name: node.theorem_name.clone(),
            lean_statement: node.lean_statement.clone(),
            statement_hash: node.statement_hash.clone(),
            is_root,
            dependency_theorem_names: dep_names.clone(),
        });
        manifest.push(DeclarationManifestEntry {
            order,
            theorem_name: node.theorem_name.clone(),
            statement_hash: node.statement_hash.clone(),
            is_root,
            dependency_theorem_names: dep_names,
        });
    }

    let declaration_manifest_hash = crate::hashing::canonical_hash(&manifest)
        .map_err(|detail| ClosureError::GraphQueryFailed { detail })?;

    Ok(OrderedClosure {
        root_obligation_id: root_id,
        root_theorem_name,
        root_statement_hash,
        environment_hash,
        declarations,
        declaration_manifest: manifest,
        declaration_manifest_hash,
    })
}

/// BFS the obligation-edge DAG from the root, requiring every reached obligation
/// to carry a positive verified lemma.
fn gather_closure(
    conn: &Connection,
    episode_id: Uuid,
    root_obligation_id: Uuid,
) -> Result<Vec<ClosureNode>, ClosureError> {
    let root_id = root_obligation_id.to_string();
    let episode = episode_id.to_string();

    // The root must at least exist in this episode.
    let root_exists: Option<String> = conn
        .query_row(
            "SELECT id FROM episode_obligations WHERE id = ?1 AND episode_id = ?2",
            [&root_id, &episode],
            |row| row.get(0),
        )
        .optional()
        .map_err(db_err)?;
    if root_exists.is_none() {
        return Err(ClosureError::RootNotFound {
            obligation_id: root_id,
        });
    }

    let mut visited: BTreeSet<String> = BTreeSet::new();
    let mut queue: VecDeque<String> = VecDeque::new();
    let mut nodes: Vec<ClosureNode> = Vec::new();
    queue.push_back(root_id.clone());
    visited.insert(root_id.clone());

    while let Some(obl_id) = queue.pop_front() {
        // Obligation identity + statement text (assemble_module needs the text).
        let obl: Option<(String, String, String)> = conn
            .query_row(
                "SELECT theorem_name, lean_statement, statement_hash
                 FROM episode_obligations WHERE id = ?1",
                [&obl_id],
                |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
            )
            .optional()
            .map_err(db_err)?;
        let (theorem_name, lean_statement, statement_hash) = match obl {
            Some(o) => o,
            None => {
                return Err(ClosureError::UnverifiedDependency {
                    obligation_id: obl_id,
                    theorem_name: None,
                })
            }
        };

        // Require a positive verified lemma — its environment is authoritative.
        let environment_hash: Option<String> = conn
            .query_row(
                "SELECT environment_hash FROM episode_verified_lemmas
                 WHERE obligation_id = ?1 AND polarity = 'positive'",
                [&obl_id],
                |row| row.get(0),
            )
            .optional()
            .map_err(db_err)?;
        let environment_hash = match environment_hash {
            Some(e) => e,
            None => {
                return Err(ClosureError::UnverifiedDependency {
                    obligation_id: obl_id,
                    theorem_name: Some(theorem_name),
                })
            }
        };

        // Direct dependencies from the obligation-edge DAG.
        let mut stmt = conn
            .prepare(
                "SELECT dependency_obligation_id FROM episode_obligation_edges
                 WHERE parent_obligation_id = ?1 ORDER BY dependency_obligation_id",
            )
            .map_err(db_err)?;
        let dep_ids: Vec<String> = stmt
            .query_map([&obl_id], |row| row.get::<_, String>(0))
            .and_then(|rows| rows.collect::<rusqlite::Result<Vec<_>>>())
            .map_err(db_err)?;

        for dep in &dep_ids {
            if visited.insert(dep.clone()) {
                queue.push_back(dep.clone());
            }
        }

        nodes.push(ClosureNode {
            obligation_id: obl_id,
            theorem_name,
            lean_statement,
            statement_hash,
            environment_hash,
            dependency_obligation_ids: dep_ids,
        });
    }

    Ok(nodes)
}

/// No two declarations may share a theorem name — Lean would see a duplicate (or
/// conflicting) declaration in one module.
fn check_interfaces(nodes: &[ClosureNode]) -> Result<(), ClosureError> {
    let mut seen: HashMap<&str, &str> = HashMap::new();
    for node in nodes {
        if let Some(prev_hash) = seen.insert(&node.theorem_name, &node.statement_hash) {
            return Err(ClosureError::IncompatibleInterface {
                theorem_name: node.theorem_name.clone(),
                statement_hash_a: prev_hash.to_string(),
                statement_hash_b: node.statement_hash.clone(),
            });
        }
    }
    Ok(())
}

/// Every declaration must share one pinned environment (the root's).
fn check_environment(nodes: &[ClosureNode]) -> Result<(), ClosureError> {
    let Some(first) = nodes.first() else {
        return Ok(());
    };
    let expected = &first.environment_hash;
    for node in nodes {
        if &node.environment_hash != expected {
            return Err(ClosureError::EnvironmentMismatch {
                theorem_name: node.theorem_name.clone(),
                expected_environment_hash: expected.clone(),
                found_environment_hash: node.environment_hash.clone(),
            });
        }
    }
    Ok(())
}

/// Deterministic Kahn topological sort — dependencies strictly before
/// dependents, ties broken by theorem name (then obligation id) so identical
/// graphs always produce identical orderings. Returns `Cycle` (with a
/// reconstructed name path) when the graph is not a DAG.
fn topological_order(nodes: &[ClosureNode]) -> Result<Vec<ClosureNode>, ClosureError> {
    let in_closure: BTreeSet<&str> = nodes.iter().map(|n| n.obligation_id.as_str()).collect();
    let by_id: HashMap<&str, &ClosureNode> = nodes
        .iter()
        .map(|n| (n.obligation_id.as_str(), n))
        .collect();

    // in_degree = number of dependencies (within the closure).
    let mut in_degree: HashMap<&str, usize> = HashMap::new();
    // dependents: dependency -> [things that depend on it].
    let mut dependents: HashMap<&str, Vec<&str>> = HashMap::new();
    for node in nodes {
        let deps: Vec<&str> = node
            .dependency_obligation_ids
            .iter()
            .map(|s| s.as_str())
            .filter(|d| in_closure.contains(d))
            .collect();
        in_degree.insert(node.obligation_id.as_str(), deps.len());
        for dep in deps {
            dependents
                .entry(dep)
                .or_default()
                .push(node.obligation_id.as_str());
        }
    }

    // Ready set keyed by (theorem_name, obligation_id) for deterministic order.
    let mut ready: BTreeMap<(&str, &str), &str> = BTreeMap::new();
    for node in nodes {
        if in_degree[node.obligation_id.as_str()] == 0 {
            ready.insert(
                (node.theorem_name.as_str(), node.obligation_id.as_str()),
                node.obligation_id.as_str(),
            );
        }
    }

    let mut ordered: Vec<ClosureNode> = Vec::with_capacity(nodes.len());
    while let Some((&key, &id)) = ready.iter().next() {
        ready.remove(&key);
        ordered.push((*by_id[id]).clone());
        if let Some(deps) = dependents.get(id) {
            for &m in deps {
                let d = in_degree.get_mut(m).unwrap();
                *d -= 1;
                if *d == 0 {
                    let mnode = by_id[m];
                    ready.insert(
                        (mnode.theorem_name.as_str(), mnode.obligation_id.as_str()),
                        m,
                    );
                }
            }
        }
    }

    if ordered.len() != nodes.len() {
        let remaining: BTreeSet<&str> = in_closure
            .iter()
            .copied()
            .filter(|id| !ordered.iter().any(|n| n.obligation_id == *id))
            .collect();
        let cycle = reconstruct_cycle(&remaining, &by_id);
        return Err(ClosureError::Cycle {
            cycle_theorem_names: cycle,
        });
    }

    Ok(ordered)
}

/// DFS the still-unresolved sub-DAG to name a concrete cycle for the error.
fn reconstruct_cycle(
    remaining: &BTreeSet<&str>,
    by_id: &HashMap<&str, &ClosureNode>,
) -> Vec<String> {
    let start = match remaining.iter().next() {
        Some(s) => *s,
        None => return Vec::new(),
    };
    let mut stack: Vec<&str> = Vec::new();
    let mut on_stack: BTreeSet<&str> = BTreeSet::new();
    let mut cursor = start;
    loop {
        if on_stack.contains(cursor) {
            let idx = stack.iter().position(|&x| x == cursor).unwrap();
            let mut names: Vec<String> = stack[idx..]
                .iter()
                .map(|id| by_id[*id].theorem_name.clone())
                .collect();
            names.push(by_id[cursor].theorem_name.clone());
            return names;
        }
        stack.push(cursor);
        on_stack.insert(cursor);
        let node = by_id[cursor];
        let next = node
            .dependency_obligation_ids
            .iter()
            .map(|s| s.as_str())
            .find(|d| remaining.contains(d));
        match next {
            Some(n) => cursor = n,
            None => {
                return stack
                    .iter()
                    .map(|id| by_id[*id].theorem_name.clone())
                    .collect()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::Utc;

    fn setup() -> (Connection, Uuid) {
        let conn = Connection::open_in_memory().unwrap();
        crate::db::initialize_db(&conn).unwrap();
        let pv = Uuid::new_v4();
        conn.execute(
            "INSERT INTO problem_versions (
                id, source_problem_text, source_problem_hash, source_metadata_json,
                root_formal_statement, root_statement_hash, normalized_root_rendering,
                environment_hash, fidelity_status, fidelity_method, state, created_at
            ) VALUES (?1, 'src', 'srch', '{}', 'stmt', 'stmth', 'render', 'envh', 'unreviewed', 'manual', 'CREATED', ?2)",
            (pv.to_string(), Utc::now().to_rfc3339()),
        ).unwrap();
        let ep = Uuid::new_v4();
        conn.execute(
            "INSERT INTO episodes (id, problem_version_id, state, created_at)
             VALUES (?1, ?2, 'awaiting_external_action', ?3)",
            (ep.to_string(), pv.to_string(), Utc::now().to_rfc3339()),
        )
        .unwrap();
        (conn, ep)
    }

    /// Seed an obligation + its positive verified lemma. `verified=false` leaves
    /// it unproved (no lemma). Returns the obligation id.
    fn seed(
        conn: &Connection,
        ep: Uuid,
        name: &str,
        stmt_hash: &str,
        env: &str,
        verified: bool,
    ) -> Uuid {
        let pv: String = conn
            .query_row(
                "SELECT problem_version_id FROM episodes WHERE id = ?1",
                [ep.to_string()],
                |r| r.get(0),
            )
            .unwrap();
        let obl = Uuid::new_v4();
        conn.execute(
            "INSERT INTO episode_obligations (
                id, episode_id, problem_version_id, kind, theorem_name, lean_statement, statement_hash,
                natural_description, status, depth_from_root, created_by, created_at
            ) VALUES (?1, ?2, ?3, 'proof', ?4, 'True', ?5, 'n', 'open', 0, 'initial_sketch', ?6)",
            (obl.to_string(), ep.to_string(), pv, name, stmt_hash, Utc::now().to_rfc3339()),
        ).unwrap();
        if verified {
            let lemma = Uuid::new_v4();
            conn.execute(
                "INSERT INTO episode_verified_lemmas (
                    id, episode_id, obligation_id, polarity, theorem_name, statement_hash,
                    proof_source_artifact_hash, compiled_artifact_hash, proof_term_hash,
                    environment_hash, actual_dependency_ids_json, kernel_result_hash, verified_at
                ) VALUES (?1, ?2, ?3, 'positive', ?4, ?5, '', 'c', 'p', ?6, '[]', 'k', ?7)",
                (
                    lemma.to_string(),
                    ep.to_string(),
                    obl.to_string(),
                    name,
                    stmt_hash,
                    env,
                    Utc::now().to_rfc3339(),
                ),
            )
            .unwrap();
            conn.execute(
                "UPDATE episode_obligations SET status = 'proved', proved_lemma_id = ?1 WHERE id = ?2",
                (lemma.to_string(), obl.to_string()),
            ).unwrap();
        }
        obl
    }

    fn edge(conn: &Connection, parent: Uuid, dep: Uuid) {
        conn.execute(
            "INSERT INTO episode_obligation_edges (parent_obligation_id, dependency_obligation_id, edge_kind, created_at)
             VALUES (?1, ?2, 'lemma', ?3)",
            (parent.to_string(), dep.to_string(), Utc::now().to_rfc3339()),
        ).unwrap();
    }

    fn order(closure: &OrderedClosure) -> Vec<&str> {
        closure
            .declarations
            .iter()
            .map(|d| d.theorem_name.as_str())
            .collect()
    }

    #[test]
    fn linear_chain_orders_dependencies_first_root_last() {
        let (conn, ep) = setup();
        let a = seed(&conn, ep, "A", "ha", "env", true);
        let b = seed(&conn, ep, "B", "hb", "env", true);
        let c = seed(&conn, ep, "C", "hc", "env", true);
        edge(&conn, a, b); // A depends on B
        edge(&conn, b, c); // B depends on C
        let closure = order_closure(&conn, ep, a).unwrap();
        assert_eq!(order(&closure), vec!["C", "B", "A"]);
        assert_eq!(closure.root_theorem_name, "A");
        assert!(closure.declarations.last().unwrap().is_root);
        assert_eq!(closure.declaration_manifest.len(), 3);
    }

    #[test]
    fn diamond_places_shared_dependency_before_both_users() {
        let (conn, ep) = setup();
        let a = seed(&conn, ep, "A", "ha", "env", true);
        let b = seed(&conn, ep, "B", "hb", "env", true);
        let c = seed(&conn, ep, "C", "hc", "env", true);
        let d = seed(&conn, ep, "D", "hd", "env", true);
        edge(&conn, a, b);
        edge(&conn, a, c);
        edge(&conn, b, d);
        edge(&conn, c, d);
        let closure = order_closure(&conn, ep, a).unwrap();
        let pos = |name: &str| {
            closure
                .declarations
                .iter()
                .position(|x| x.theorem_name == name)
                .unwrap()
        };
        assert!(pos("D") < pos("B") && pos("D") < pos("C"));
        assert!(pos("B") < pos("A") && pos("C") < pos("A"));
    }

    #[test]
    fn ordering_is_deterministic_for_the_same_graph() {
        let (conn, ep) = setup();
        let a = seed(&conn, ep, "A", "ha", "env", true);
        let b = seed(&conn, ep, "B", "hb", "env", true);
        let c = seed(&conn, ep, "C", "hc", "env", true);
        edge(&conn, a, b);
        edge(&conn, a, c);
        let first = order_closure(&conn, ep, a).unwrap();
        let second = order_closure(&conn, ep, a).unwrap();
        assert_eq!(
            first.declaration_manifest_hash,
            second.declaration_manifest_hash
        );
        assert_eq!(order(&first), order(&second));
    }

    #[test]
    fn unverified_dependency_is_a_structured_error() {
        let (conn, ep) = setup();
        let a = seed(&conn, ep, "A", "ha", "env", true);
        let b = seed(&conn, ep, "B", "hb", "env", false); // no verified lemma
        edge(&conn, a, b);
        match order_closure(&conn, ep, a).unwrap_err() {
            ClosureError::UnverifiedDependency { theorem_name, .. } => {
                assert_eq!(theorem_name.as_deref(), Some("B"));
            }
            other => panic!("expected UnverifiedDependency, got {other:?}"),
        }
    }

    #[test]
    fn cycle_is_detected_and_named() {
        let (conn, ep) = setup();
        let a = seed(&conn, ep, "A", "ha", "env", true);
        let b = seed(&conn, ep, "B", "hb", "env", true);
        edge(&conn, a, b);
        edge(&conn, b, a); // cycle
        match order_closure(&conn, ep, a).unwrap_err() {
            ClosureError::Cycle {
                cycle_theorem_names,
            } => {
                assert!(cycle_theorem_names.contains(&"A".to_string()));
                assert!(cycle_theorem_names.contains(&"B".to_string()));
            }
            other => panic!("expected Cycle, got {other:?}"),
        }
    }

    #[test]
    fn environment_mismatch_is_rejected() {
        let (conn, ep) = setup();
        let a = seed(&conn, ep, "A", "ha", "env1", true);
        let b = seed(&conn, ep, "B", "hb", "env2", true); // different env
        edge(&conn, a, b);
        assert!(matches!(
            order_closure(&conn, ep, a).unwrap_err(),
            ClosureError::EnvironmentMismatch { .. }
        ));
    }

    #[test]
    fn missing_root_is_reported() {
        let (conn, ep) = setup();
        let ghost = Uuid::new_v4();
        assert!(matches!(
            order_closure(&conn, ep, ghost).unwrap_err(),
            ClosureError::RootNotFound { .. }
        ));
    }

    #[test]
    fn declarations_carry_statement_text_and_dependency_names() {
        let (conn, ep) = setup();
        let a = seed(&conn, ep, "A", "ha", "env", true);
        let b = seed(&conn, ep, "B", "hb", "env", true);
        edge(&conn, a, b);
        let closure = order_closure(&conn, ep, a).unwrap();
        let root = closure.declarations.iter().find(|d| d.is_root).unwrap();
        assert_eq!(root.theorem_name, "A");
        assert_eq!(root.lean_statement, "True");
        assert_eq!(root.dependency_theorem_names, vec!["B".to_string()]);
    }
}
