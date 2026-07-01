use std::collections::{HashMap, HashSet, VecDeque};
use crate::models::{Obligation, ObligationStatus, ObligationKind};
use rusqlite::Connection;
use uuid::Uuid;

fn estimate_difficulty(lean_statement: &str, attempt_count: i64) -> f64 {
    let characters = lean_statement.len();
    let lean_ast_nodes = (characters / 5) as f64; // rough estimate

    let mut binder_depth = 0;
    for word in lean_statement.split_whitespace() {
        if word.contains('∀') || word.contains('∃') || word.contains("fun") || word.contains("→") || word.contains("forall") || word.contains("exists") {
            binder_depth += 1;
        }
    }

    let mut logical_branch_count = 0;
    for word in lean_statement.split_whitespace() {
        if word.contains('∧') || word.contains('∨') || word.contains("if") || word.contains("and") || word.contains("or") {
            logical_branch_count += 1;
        }
    }

    let typeclass_or_synthesis_failures: f64 = 0.0;
    let semantic_failure_count = attempt_count as f64;
    let max_attempts = 6.0;

    let term1 = 0.25 * (lean_ast_nodes / 200.0).min(1.0);
    let term2 = 0.20 * (binder_depth as f64 / 8.0).min(1.0);
    let term3 = 0.15 * (logical_branch_count as f64 / 8.0).min(1.0);
    let term4 = 0.15 * (typeclass_or_synthesis_failures / 4.0).min(1.0);
    let term5 = 0.25 * (semantic_failure_count / max_attempts).min(1.0);

    (term1 + term2 + term3 + term4 + term5).clamp(0.0, 1.0)
}

fn get_edges_for_problem(
    conn: &Connection,
    problem_id: Uuid,
) -> rusqlite::Result<Vec<(Uuid, Uuid)>> {
    let mut stmt = conn.prepare(
        "SELECT parent_obligation_id, dependency_obligation_id
         FROM obligation_edges
         WHERE parent_obligation_id IN (
             SELECT id FROM obligations WHERE problem_version_id = ?1
         )"
    )?;
    let rows = stmt.query_map([problem_id.to_string()], |row| {
        let parent_str: String = row.get(0)?;
        let dep_str: String = row.get(1)?;
        let p_id = Uuid::parse_str(&parent_str).map_err(|e| {
            rusqlite::Error::FromSqlConversionFailure(0, rusqlite::types::Type::Text, Box::new(e))
        })?;
        let d_id = Uuid::parse_str(&dep_str).map_err(|e| {
            rusqlite::Error::FromSqlConversionFailure(1, rusqlite::types::Type::Text, Box::new(e))
        })?;
        Ok((p_id, d_id))
    })?;
    let mut vec = Vec::new();
    for r in rows {
        vec.push(r?);
    }
    Ok(vec)
}

pub fn next_ready(
    conn: &Connection,
    problem_version_id: Uuid,
    remaining_budget: f64,
) -> Result<Option<Obligation>, String> {
    // 1. Fetch obligations
    let obligations = crate::db::get_obligations_for_problem(conn, problem_version_id)
        .map_err(|e| format!("DB error: {}", e))?;

    // 2. Fetch edges
    let edges = get_edges_for_problem(conn, problem_version_id)
        .map_err(|e| format!("DB error: {}", e))?;

    // Construct maps
    let o_map: HashMap<Uuid, &Obligation> = obligations.iter().map(|o| (o.id, o)).collect();
    
    // parent -> list of dependencies
    let mut adj: HashMap<Uuid, Vec<Uuid>> = HashMap::new();
    // dependency -> list of parents
    let mut rev_adj: HashMap<Uuid, Vec<Uuid>> = HashMap::new();

    for &(p, d) in &edges {
        adj.entry(p).or_default().push(d);
        rev_adj.entry(d).or_default().push(p);
    }

    // Find the root obligation
    let root_opt = obligations.iter().find(|o| matches!(o.kind, ObligationKind::Root));
    let root_id = match root_opt {
        Some(r) => r.id,
        None => return Ok(None), // No root obligation found
    };

    // Filter active obligations: status is NOT superseded, abandoned, or blocked_needs_human
    let active_statuses = [
        ObligationStatus::Open,
        ObligationStatus::InProgress,
        ObligationStatus::Proved,
        ObligationStatus::Refuted,
    ];
    let is_active = |o_id: &Uuid| -> bool {
        if let Some(o) = o_map.get(o_id) {
            active_statuses.contains(&o.status)
        } else {
            false
        }
    };

    // 3. Find ready obligations
    // Ready if: status == open, AND every direct dependency is proved,
    // AND it is active, and its transitive dependencies are active
    let mut ready_obligations = Vec::new();
    for o in &obligations {
        if o.status != ObligationStatus::Open {
            continue;
        }
        // Direct dependencies must all be proved
        let deps = adj.get(&o.id);
        let all_deps_proved = match deps {
            Some(d_list) => d_list.iter().all(|d_id| {
                if let Some(dep_o) = o_map.get(d_id) {
                    dep_o.status == ObligationStatus::Proved
                } else {
                    false
                }
            }),
            None => true, // Leaf obligation is ready
        };

        if all_deps_proved {
            ready_obligations.push(o);
        }
    }

    if ready_obligations.is_empty() {
        return Ok(None);
    }

    // 4. Compute scoring variables

    // C(o): paths_to_root(o)
    // We compute paths_to_root for all active obligations using dynamic programming / memoization.
    let mut memo_paths: HashMap<Uuid, u64> = HashMap::new();
    memo_paths.insert(root_id, 1);

    // To compute paths_to_root, we can do DFS from the target obligation up to root
    fn count_paths_to_root(
        node: Uuid,
        root: Uuid,
        rev_adj: &HashMap<Uuid, Vec<Uuid>>,
        is_active: &dyn Fn(&Uuid) -> bool,
        memo: &mut HashMap<Uuid, u64>,
        visited: &mut HashSet<Uuid>,
    ) -> u64 {
        if node == root {
            return 1;
        }
        if !is_active(&node) {
            return 0;
        }
        if let Some(&val) = memo.get(&node) {
            return val;
        }
        if visited.contains(&node) {
            // Cycle detected! Safely return 0.
            return 0;
        }
        visited.insert(node);

        let mut sum = 0;
        if let Some(parents) = rev_adj.get(&node) {
            for &p in parents {
                sum += count_paths_to_root(p, root, rev_adj, is_active, memo, visited);
            }
        }

        visited.remove(&node);
        memo.insert(node, sum);
        sum
    }

    let mut max_paths = 1;
    let mut paths_map = HashMap::new();
    for o in &obligations {
        if is_active(&o.id) {
            let mut visited = HashSet::new();
            let p_count = count_paths_to_root(o.id, root_id, &rev_adj, &is_active, &mut memo_paths, &mut visited);
            paths_map.insert(o.id, p_count);
            if p_count > max_paths {
                max_paths = p_count;
            }
        }
    }

    // D(o): min_distance_to_root(o)
    // BFS starting from root forward (parent to dependency)
    let mut dist_map: HashMap<Uuid, u64> = HashMap::new();
    dist_map.insert(root_id, 0);
    let mut queue = VecDeque::new();
    queue.push_back(root_id);

    let mut max_dist = 0;
    while let Some(curr) = queue.pop_front() {
        let curr_dist = dist_map[&curr];
        if curr_dist > max_dist {
            max_dist = curr_dist;
        }
        if let Some(deps) = adj.get(&curr) {
            for &d in deps {
                if is_active(&d) && !dist_map.contains_key(&d) {
                    dist_map.insert(d, curr_dist + 1);
                    queue.push_back(d);
                }
            }
        }
    }

    // total_open_obligations
    let total_open_obligations = obligations.iter()
        .filter(|o| o.status == ObligationStatus::Open || o.status == ObligationStatus::InProgress)
        .count() as f64;

    // Helper for open_desc(o): Count unique active open/in_progress ancestors of `o` (recursively upward)
    let get_open_desc = |o_id: Uuid| -> f64 {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(o_id);

        let mut count = 0;
        while let Some(curr) = queue.pop_front() {
            if let Some(parents) = rev_adj.get(&curr) {
                for &p in parents {
                    if is_active(&p) && !visited.contains(&p) {
                        visited.insert(p);
                        if let Some(parent_o) = o_map.get(&p) {
                            if parent_o.status == ObligationStatus::Open || parent_o.status == ObligationStatus::InProgress {
                                count += 1;
                            }
                        }
                        queue.push_back(p);
                    }
                }
            }
        }
        count as f64
    };

    // Helper for immediate(o): Number of open obligations that become ready if `o` is proved.
    let get_immediate = |o_id: Uuid| -> f64 {
        let mut count = 0;
        if let Some(parents) = rev_adj.get(&o_id) {
            for &p in parents {
                if !is_active(&p) {
                    continue;
                }
                if let Some(parent_o) = o_map.get(&p) {
                    if parent_o.status == ObligationStatus::Open || parent_o.status == ObligationStatus::InProgress {
                        // Check if all of its OTHER dependencies are already proved
                        if let Some(p_deps) = adj.get(&p) {
                            let other_deps_proved = p_deps.iter().all(|&d| {
                                if d == o_id {
                                    true
                                } else if let Some(dep_o) = o_map.get(&d) {
                                    dep_o.status == ObligationStatus::Proved
                                } else {
                                    false
                                }
                            });
                            if other_deps_proved {
                                count += 1;
                            }
                        }
                    }
                }
            }
        }
        count as f64
    };

    let mut scored_ready: Vec<(&Obligation, f64)> = ready_obligations.iter().map(|&o| {
        let p_count = *paths_map.get(&o.id).unwrap_or(&0) as f64;
        let c_o = if max_paths > 1 {
            (1.0 + p_count).ln() / (1.0 + max_paths as f64).ln()
        } else {
            0.0
        };

        let min_dist = *dist_map.get(&o.id).unwrap_or(&0) as f64;
        let d_o = if max_dist > 0 {
            1.0 - min_dist / max_dist as f64
        } else {
            1.0
        };

        let immediate = get_immediate(o.id);
        let open_desc = get_open_desc(o.id);
        let i_o = ((immediate + 0.25 * open_desc) / total_open_obligations.max(1.0)).min(1.0);

        let h_o = estimate_difficulty(&o.lean_statement, o.attempt_count);

        let expected_next_cost = 0.05; // 0.05 USD / 50000 micros
        let remaining_budget_val = if remaining_budget > 0.0 { remaining_budget } else { 0.05 };
        let k_o = (expected_next_cost / remaining_budget_val).min(1.0);

        let score = (0.30 * c_o + 0.20 * d_o + 0.30 * i_o + 0.20 * (1.0 - h_o)) / (1.0 + k_o);
        (o, score)
    }).collect();

    // Sort scored ready obligations by score descending, then tie-breakers:
    // 1. Lower attempt count.
    // 2. Older created_at.
    // 3. Lexicographically smaller obligation UUID.
    scored_ready.sort_by(|a, b| {
        b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal)
            .then_with(|| a.0.attempt_count.cmp(&b.0.attempt_count))
            .then_with(|| a.0.created_at.cmp(&b.0.created_at))
            .then_with(|| a.0.id.cmp(&b.0.id))
    });

    Ok(scored_ready.first().map(|&(o, _)| o.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::db::{initialize_db, insert_problem_version, insert_obligation, insert_edge};
    use crate::models::{ProblemVersion, ProblemState, FidelityStatus, ObligationKind, ObligationCreator, ObligationEdge, EdgeKind};
    use chrono::Utc;

    #[test]
    fn test_next_ready_scheduling() {
        let conn = Connection::open_in_memory().unwrap();
        initialize_db(&conn).unwrap();

        let problem_id = Uuid::new_v4();
        let pv = ProblemVersion {
            id: problem_id,
            source_problem_text: "Prove x + 0 = x".to_string(),
            source_problem_hash: "hash1".to_string(),
            source_metadata_json: "{}".to_string(),
            root_formal_statement: "theorem root (x : Int) : x + 0 = x".to_string(),
            root_statement_hash: "hash2".to_string(),
            normalized_root_rendering: "x + 0 = x".to_string(),
            environment_hash: "envhash".to_string(),
            fidelity_status: FidelityStatus::Approved,
            fidelity_method: "human_authored".to_string(),
            fidelity_approval_id: None,
            root_obligation_id: None,
            state: ProblemState::Proving,
            created_at: Utc::now(),
        };
        insert_problem_version(&conn, &pv).unwrap();

        let root_id = Uuid::new_v4();
        let o_root = Obligation {
            id: root_id,
            problem_version_id: problem_id,
            kind: ObligationKind::Root,
            theorem_name: "O_root".to_string(),
            lean_statement: "x + 0 = x".to_string(),
            statement_hash: "hash2".to_string(),
            natural_description: "root".to_string(),
            status: ObligationStatus::Open,
            depth_from_root: 0,
            created_by: ObligationCreator::InitialSketch,
            created_by_epoch_id: None,
            superseded_by_id: None,
            proved_lemma_id: None,
            refutation_lemma_id: None,
            failure_lesson: None,
            attempt_count: 0,
            created_at: Utc::now(),
            closed_at: None,
        };
        insert_obligation(&conn, &o_root).unwrap();

        // 1. Root has an open dependency child1
        let child1_id = Uuid::new_v4();
        let o_child1 = Obligation {
            id: child1_id,
            problem_version_id: problem_id,
            kind: ObligationKind::Proof,
            theorem_name: "O_child1".to_string(),
            lean_statement: "x + 0 = x".to_string(),
            statement_hash: "hash3".to_string(),
            natural_description: "child1".to_string(),
            status: ObligationStatus::Open,
            depth_from_root: 1,
            created_by: ObligationCreator::InitialSketch,
            created_by_epoch_id: None,
            superseded_by_id: None,
            proved_lemma_id: None,
            refutation_lemma_id: None,
            failure_lesson: None,
            attempt_count: 0,
            created_at: Utc::now(),
            closed_at: None,
        };
        insert_obligation(&conn, &o_child1).unwrap();

        let edge = ObligationEdge {
            parent_obligation_id: root_id,
            dependency_obligation_id: child1_id,
            edge_kind: EdgeKind::Lemma,
            case_group: None,
            created_at: Utc::now(),
        };
        insert_edge(&conn, &edge).unwrap();

        // Currently, root depends on child1, so only child1 is ready because all its dependencies (none) are proved.
        // Root is NOT ready because child1 is not proved.
        let ready = next_ready(&conn, problem_id, 1.0).unwrap();
        assert!(ready.is_some());
        assert_eq!(ready.unwrap().id, child1_id);

        // Now, let's add child2, so root depends on child1 and child2.
        let child2_id = Uuid::new_v4();
        let o_child2 = Obligation {
            id: child2_id,
            problem_version_id: problem_id,
            kind: ObligationKind::Proof,
            theorem_name: "O_child2".to_string(),
            lean_statement: "y + 0 = y".to_string(),
            statement_hash: "hash4".to_string(),
            natural_description: "child2".to_string(),
            status: ObligationStatus::Open,
            depth_from_root: 1,
            created_by: ObligationCreator::InitialSketch,
            created_by_epoch_id: None,
            superseded_by_id: None,
            proved_lemma_id: None,
            refutation_lemma_id: None,
            failure_lesson: None,
            attempt_count: 0,
            created_at: Utc::now() + chrono::Duration::seconds(5),
            closed_at: None,
        };
        insert_obligation(&conn, &o_child2).unwrap();

        let edge2 = ObligationEdge {
            parent_obligation_id: root_id,
            dependency_obligation_id: child2_id,
            edge_kind: EdgeKind::Lemma,
            case_group: None,
            created_at: Utc::now(),
        };
        insert_edge(&conn, &edge2).unwrap();

        // Both child1 and child2 are ready.
        // Since child1 is created earlier and has smaller UUID/difficulty etc, it should score higher or break ties.
        // Let's verify next_ready returns child1.
        let ready2 = next_ready(&conn, problem_id, 1.0).unwrap();
        assert!(ready2.is_some());
        assert_eq!(ready2.unwrap().id, child1_id);
    }
}
