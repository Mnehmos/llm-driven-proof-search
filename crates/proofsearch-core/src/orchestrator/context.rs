use crate::models::Obligation;
use rusqlite::{Connection, OptionalExtension};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use uuid::Uuid;

/// Default conservative bytes-per-token divisor used to convert a token budget
/// into a byte ceiling (#223). English prose is ~4 bytes/token; dense Lean can
/// be denser, so this is configurable per builder.
pub const DEFAULT_BYTES_PER_TOKEN: usize = 4;

/// Bytes of the latest primary diagnostic that are ALWAYS inlined, even when the
/// core has already exhausted the budget. Guarantees the "always include latest
/// primary diagnostic" acceptance criterion (#223).
pub const DIAGNOSTIC_HEAD_BYTES: usize = 512;

/// Logical field of a budgeted observation that may be truncated/omitted and
/// later retrieved through pagination (#223).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum ObservationField {
    /// The full root theorem signature.
    RootTheorem,
    /// The newline-joined full signatures of the direct dependencies.
    DependencySignatures,
    /// The complete latest primary diagnostic JSON.
    Diagnostics,
    /// Historical failure lessons for the current obligation.
    ProofHistory,
}

impl ObservationField {
    pub fn as_str(&self) -> &'static str {
        match self {
            ObservationField::RootTheorem => "root_theorem",
            ObservationField::DependencySignatures => "dependency_signatures",
            ObservationField::Diagnostics => "diagnostics",
            ObservationField::ProofHistory => "proof_history",
        }
    }
}

/// A stable pointer to observation material that did not fully fit the budget,
/// plus the offset a client passes to `observation_expand` to page the rest.
/// Emitted whenever a field is truncated or omitted — omitted content is always
/// referenced, never silently discarded (#223).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct ContentReference {
    pub field: ObservationField,
    /// SHA-256 (hex) of the FULL field content. Stable across pagination so a
    /// client can detect if the underlying material changed between pages.
    pub content_hash: String,
    /// Full size of the field content in bytes.
    pub total_bytes: usize,
    /// Bytes inlined as a prefix in this observation (0 if fully omitted).
    pub included_bytes: usize,
    /// Byte offset to pass to `observation_expand` to fetch the next page.
    /// Always equals `included_bytes`; present for explicitness.
    pub next_offset: usize,
}

/// Conservative accounting of what an observation includes, omits, and
/// references (#223). All figures are UTF-8 byte counts (bytes >= tokens, so
/// byte accounting never under-counts the real token cost).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct ObservationBudget {
    /// Byte ceiling this observation was assembled against.
    pub max_observation_bytes: usize,
    /// Bytes actually inlined in the observation (core + inlined prefixes).
    pub included_bytes: usize,
    /// Bytes of existing material NOT inlined (retrievable via `references`).
    pub omitted_bytes: usize,
    /// Total bytes of all material behind a `ContentReference`
    /// (inlined prefix + omitted tail).
    pub referenced_bytes: usize,
    /// True iff any material was omitted (i.e. `references` is non-empty).
    pub truncated: bool,
    /// Conservative bytes-per-token divisor used to derive the byte ceiling.
    pub bytes_per_token: usize,
}

/// Always-included per-dependency core (name + status + statement hash),
/// independent of whether the full signature is inlined (#223).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct DependencySummary {
    pub theorem_name: String,
    pub status: String,
    pub statement_hash: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct CompactContext {
    pub env_id: String,
    /// Immutable per problem_version. An `unknown identifier` result under this
    /// exact manifest establishes only that the name didn't resolve HERE — never
    /// that it's absent from the pinned library. Use lean_declaration_lookup to
    /// tell the difference before concluding an API is missing.
    pub import_manifest_hash: String,
    /// Conditionally inlined (#223): a prefix of the root theorem when it does
    /// not fully fit the budget. The full text is then reachable via a
    /// `RootTheorem` reference in `references`.
    pub root_theorem_signature: String,
    /// Always included in full — the obligation currently being worked.
    pub obligation_signature: String,
    /// Statement hash of the current obligation (always included; #223 core).
    pub obligation_statement_hash: String,
    /// Fully-inlined direct dependency signatures. If the budget could not fit
    /// them all, the remainder is referenced via a `DependencySignatures`
    /// reference and this vec holds only the ones that fit (#223).
    pub direct_dependency_signatures: Vec<String>,
    /// Name + status + statement hash for every direct dependency — always
    /// present regardless of whether the full signature was inlined (#223 core).
    pub direct_dependencies: Vec<DependencySummary>,
    /// A bounded head of the latest primary diagnostic (always present when a
    /// diagnostic exists); the complete diagnostic is reachable via a
    /// `Diagnostics` reference when truncated (#223).
    pub latest_diagnostic: Option<String>,
    pub distilled_lesson: Option<String>,
    pub retrieved_hint: Option<String>,
    /// Stable pointers to omitted/truncated material with continuation offsets.
    pub references: Vec<ContentReference>,
    /// Conservative byte accounting of the assembled observation.
    pub budget: ObservationBudget,
}

/// A page of previously-omitted observation material retrieved through the
/// deterministic pagination API (#223).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct ObservationPage {
    pub field: ObservationField,
    /// SHA-256 (hex) of the full field content (matches the emitting reference).
    pub content_hash: String,
    /// Full size of the field content in bytes.
    pub total_bytes: usize,
    /// Byte offset this page starts at.
    pub offset: usize,
    /// The requested slice `[offset, offset+limit)`, clamped to char boundaries.
    pub bytes: String,
    /// Next offset to request, or `None` when the end has been reached.
    pub next_offset: Option<usize>,
}

/// SHA-256 hex of raw field content, used as a stable cross-page identifier.
fn content_hash(content: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(content.as_bytes());
    format!("{:x}", hasher.finalize())
}

/// Largest index `<= idx` that lies on a UTF-8 char boundary of `s`.
fn floor_char_boundary(s: &str, idx: usize) -> usize {
    if idx >= s.len() {
        return s.len();
    }
    let mut i = idx;
    while i > 0 && !s.is_char_boundary(i) {
        i -= 1;
    }
    i
}

/// Raw, un-budgeted observation material gathered from the store, prior to
/// prioritized assembly.
struct RawObservation {
    env_id: String,
    import_manifest_hash: String,
    obligation_signature: String,
    obligation_statement_hash: String,
    root_theorem_signature: String,
    dependency_summaries: Vec<DependencySummary>,
    dependency_full_signatures: Vec<String>,
    latest_diagnostic: Option<String>,
    distilled_lesson: Option<String>,
    retrieved_hint: Option<String>,
}

pub struct CompactContextBuilder {
    pub max_context_tokens: usize,
    /// Conservative bytes-per-token divisor (#223). Configurable; a smaller
    /// value is more conservative (allows fewer bytes per token of budget).
    pub bytes_per_token: usize,
}

impl CompactContextBuilder {
    pub fn new(max_context_tokens: usize) -> Self {
        Self {
            max_context_tokens,
            bytes_per_token: DEFAULT_BYTES_PER_TOKEN,
        }
    }

    /// Construct with an explicit, configurable byte-accounting ratio (#223).
    pub fn with_bytes_per_token(max_context_tokens: usize, bytes_per_token: usize) -> Self {
        Self {
            max_context_tokens,
            bytes_per_token: bytes_per_token.max(1),
        }
    }

    /// Byte ceiling every default observation must fit within (#223).
    pub fn max_observation_bytes(&self) -> usize {
        self.max_context_tokens
            .saturating_mul(self.bytes_per_token.max(1))
    }

    /// Prioritized, never-failing assembly of the raw material into a budgeted
    /// observation. Core (env/manifest hashes, current obligation + its hash,
    /// dependency summaries, latest diagnostic head) is always included;
    /// remaining budget is spent inlining full material in priority order, and
    /// anything that does not fit is replaced with a stable reference plus a
    /// continuation offset. Never returns `CONTEXT_TOO_LARGE` (#223).
    fn assemble(&self, raw: RawObservation) -> CompactContext {
        let max = self.max_observation_bytes();
        let mut used: usize = 0;
        let mut references: Vec<ContentReference> = Vec::new();
        let mut omitted_bytes: usize = 0;
        let mut referenced_bytes: usize = 0;

        // --- Core: always included in full ---
        used += raw.env_id.len()
            + raw.import_manifest_hash.len()
            + raw.obligation_signature.len()
            + raw.obligation_statement_hash.len();
        for d in &raw.dependency_summaries {
            used += d.theorem_name.len() + d.status.len() + d.statement_hash.len();
        }

        // --- Conditional field 1 (highest priority): full root theorem ---
        let root_theorem_signature = Self::place_prefix_field(
            ObservationField::RootTheorem,
            &raw.root_theorem_signature,
            0,
            max,
            &mut used,
            &mut references,
            &mut omitted_bytes,
            &mut referenced_bytes,
        );

        // --- Conditional field 2: full dependency signatures (whole-sig greedy) ---
        let direct_dependency_signatures = self.place_dependency_signatures(
            &raw.dependency_full_signatures,
            max,
            &mut used,
            &mut references,
            &mut omitted_bytes,
            &mut referenced_bytes,
        );

        // --- Conditional field 3: complete diagnostics (with guaranteed head) ---
        let latest_diagnostic = match &raw.latest_diagnostic {
            Some(full) if !full.is_empty() => Some(Self::place_prefix_field(
                ObservationField::Diagnostics,
                full,
                DIAGNOSTIC_HEAD_BYTES,
                max,
                &mut used,
                &mut references,
                &mut omitted_bytes,
                &mut referenced_bytes,
            )),
            _ => None,
        };

        // --- Conditional field 4 (lowest priority): historical failure lessons ---
        let distilled_lesson = match &raw.distilled_lesson {
            Some(full) if !full.is_empty() => Some(Self::place_prefix_field(
                ObservationField::ProofHistory,
                full,
                0,
                max,
                &mut used,
                &mut references,
                &mut omitted_bytes,
                &mut referenced_bytes,
            )),
            _ => None,
        };

        let budget = ObservationBudget {
            max_observation_bytes: max,
            included_bytes: used,
            omitted_bytes,
            referenced_bytes,
            truncated: !references.is_empty(),
            bytes_per_token: self.bytes_per_token.max(1),
        };

        CompactContext {
            env_id: raw.env_id,
            import_manifest_hash: raw.import_manifest_hash,
            root_theorem_signature,
            obligation_signature: raw.obligation_signature,
            obligation_statement_hash: raw.obligation_statement_hash,
            direct_dependency_signatures,
            direct_dependencies: raw.dependency_summaries,
            latest_diagnostic,
            distilled_lesson,
            retrieved_hint: raw.retrieved_hint,
            references,
            budget,
        }
    }

    /// Inline a byte-prefix of `content` that fits the remaining budget (but at
    /// least `min_head` bytes even if the budget is already exhausted). Emits a
    /// reference for whatever was not inlined. Returns the inlined prefix.
    #[allow(clippy::too_many_arguments)]
    fn place_prefix_field(
        field: ObservationField,
        content: &str,
        min_head: usize,
        max: usize,
        used: &mut usize,
        references: &mut Vec<ContentReference>,
        omitted_bytes: &mut usize,
        referenced_bytes: &mut usize,
    ) -> String {
        let total = content.len();
        if total == 0 {
            return String::new();
        }
        let remaining = max.saturating_sub(*used);
        let want = remaining.max(min_head).min(total);
        let take = floor_char_boundary(content, want);
        let prefix = content[..take].to_string();
        *used += take;
        if take < total {
            references.push(ContentReference {
                field,
                content_hash: content_hash(content),
                total_bytes: total,
                included_bytes: take,
                next_offset: take,
            });
            *omitted_bytes += total - take;
            *referenced_bytes += total;
        }
        prefix
    }

    /// Greedily inline whole dependency signatures while the budget allows;
    /// reference the newline-joined remainder if any do not fit.
    fn place_dependency_signatures(
        &self,
        signatures: &[String],
        max: usize,
        used: &mut usize,
        references: &mut Vec<ContentReference>,
        omitted_bytes: &mut usize,
        referenced_bytes: &mut usize,
    ) -> Vec<String> {
        if signatures.is_empty() {
            return Vec::new();
        }
        let joined_full = signatures.join("\n");
        let full_len = joined_full.len();
        let remaining = max.saturating_sub(*used);

        let mut inlined: Vec<String> = Vec::new();
        let mut consumed: usize = 0;
        for (i, sig) in signatures.iter().enumerate() {
            let sep = if i == 0 { 0 } else { 1 };
            let cost = sep + sig.len();
            if consumed + cost <= remaining {
                consumed += cost;
                inlined.push(sig.clone());
            } else {
                break;
            }
        }
        *used += consumed;

        if inlined.len() < signatures.len() {
            references.push(ContentReference {
                field: ObservationField::DependencySignatures,
                content_hash: content_hash(&joined_full),
                total_bytes: full_len,
                included_bytes: consumed,
                next_offset: consumed,
            });
            *omitted_bytes += full_len - consumed;
            *referenced_bytes += full_len;
        }
        inlined
    }

    pub fn build_episode(
        &self,
        conn: &Connection,
        episode_id: Uuid,
        obligation_id: Uuid,
        environment_hash: &str,
        import_manifest_hash: &str,
        root_formal_statement: &str,
    ) -> Result<CompactContext, String> {
        // Fetch the obligation from episode_obligations
        let mut obl_stmt = conn
            .prepare(
                "SELECT theorem_name, lean_statement, statement_hash, status, failure_lesson
             FROM episode_obligations WHERE id = ?1 AND episode_id = ?2",
            )
            .map_err(|e| e.to_string())?;

        let (theorem_name, lean_statement, statement_hash, _status, failure_lesson) = obl_stmt
            .query_row([obligation_id.to_string(), episode_id.to_string()], |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, String>(1)?,
                    row.get::<_, String>(2)?,
                    row.get::<_, String>(3)?,
                    row.get::<_, Option<String>>(4)?,
                ))
            })
            .map_err(|e| format!("Obligation not found: {}", e))?;

        let obligation_signature = format!("theorem {} : {}", theorem_name, lean_statement);

        let (dependency_summaries, dependency_full_signatures) =
            Self::episode_dependencies(conn, obligation_id)?;

        let latest_diagnostic = Self::episode_latest_diagnostic(conn, episode_id)?;

        let raw = RawObservation {
            env_id: environment_hash.to_string(),
            import_manifest_hash: import_manifest_hash.to_string(),
            obligation_signature,
            obligation_statement_hash: statement_hash,
            root_theorem_signature: root_formal_statement.to_string(),
            dependency_summaries,
            dependency_full_signatures,
            latest_diagnostic,
            distilled_lesson: failure_lesson,
            retrieved_hint: None,
        };

        Ok(self.assemble(raw))
    }

    /// Direct dependencies of an episode obligation: (summaries, full signatures).
    /// Enforces the invariant that every direct dependency is proved.
    fn episode_dependencies(
        conn: &Connection,
        obligation_id: Uuid,
    ) -> Result<(Vec<DependencySummary>, Vec<String>), String> {
        let mut stmt = conn.prepare(
            "SELECT dependency_obligation_id FROM episode_obligation_edges WHERE parent_obligation_id = ?1"
        ).map_err(|e| e.to_string())?;

        let dep_ids = stmt
            .query_map([obligation_id.to_string()], |row| row.get::<_, String>(0))
            .map_err(|e| e.to_string())?;

        let mut summaries = Vec::new();
        let mut signatures = Vec::new();
        for id_res in dep_ids {
            let id_str = id_res.map_err(|e| e.to_string())?;
            let mut o_stmt = conn.prepare(
                "SELECT theorem_name, lean_statement, statement_hash, status FROM episode_obligations WHERE id = ?1"
            ).map_err(|e| e.to_string())?;

            let (name, stmt_text, stmt_hash, status) = o_stmt
                .query_row([id_str.clone()], |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, String>(1)?,
                        row.get::<_, String>(2)?,
                        row.get::<_, String>(3)?,
                    ))
                })
                .map_err(|e| e.to_string())?;

            if status != "proved" {
                return Err(format!(
                    "Invariant violation: direct dependency {} is not proved (status={})",
                    id_str, status
                ));
            }

            summaries.push(DependencySummary {
                theorem_name: name.clone(),
                status,
                statement_hash: stmt_hash,
            });
            signatures.push(format!("theorem {} : {}", name, stmt_text));
        }
        Ok((summaries, signatures))
    }

    /// Latest rejected-attempt diagnostic for an episode, if any.
    fn episode_latest_diagnostic(
        conn: &Connection,
        episode_id: Uuid,
    ) -> Result<Option<String>, String> {
        let mut attempt_stmt = conn
            .prepare(
                "SELECT lean_result_json FROM action_attempts
             WHERE episode_id = ?1 AND status = 'rejected'
             ORDER BY execution_completed_at DESC LIMIT 1",
            )
            .map_err(|e| e.to_string())?;

        Ok(attempt_stmt
            .query_row([episode_id.to_string()], |row| {
                row.get::<_, Option<String>>(0)
            })
            .optional()
            .map_err(|e| e.to_string())?
            .flatten())
    }

    /// Deterministically re-derive and page a single observation field (#223).
    /// Content is identical to what `build_episode` would inline in full, so a
    /// reference emitted by an observation resolves to exactly this material.
    /// `limit == 0` is treated as "no limit" (return the whole remaining tail).
    pub fn expand_observation_field(
        &self,
        conn: &Connection,
        episode_id: Uuid,
        obligation_id: Uuid,
        field: ObservationField,
        offset: usize,
        limit: usize,
    ) -> Result<ObservationPage, String> {
        let content = self.derive_field_content(conn, episode_id, obligation_id, field)?;
        let total = content.len();
        let start = floor_char_boundary(&content, offset.min(total));
        let end = if limit == 0 {
            total
        } else {
            floor_char_boundary(&content, start.saturating_add(limit).min(total))
        };
        let bytes = content[start..end].to_string();
        let next_offset = if end < total { Some(end) } else { None };
        Ok(ObservationPage {
            field,
            content_hash: content_hash(&content),
            total_bytes: total,
            offset: start,
            bytes,
            next_offset,
        })
    }

    /// The full, un-truncated content of a single field for the episode path.
    fn derive_field_content(
        &self,
        conn: &Connection,
        episode_id: Uuid,
        obligation_id: Uuid,
        field: ObservationField,
    ) -> Result<String, String> {
        match field {
            ObservationField::RootTheorem => {
                let root: String = conn
                    .query_row(
                        "SELECT pv.root_formal_statement
                     FROM episodes e JOIN problem_versions pv ON e.problem_version_id = pv.id
                     WHERE e.id = ?1",
                        [episode_id.to_string()],
                        |row| row.get(0),
                    )
                    .map_err(|e| format!("root theorem not found: {}", e))?;
                Ok(root)
            }
            ObservationField::DependencySignatures => {
                let (_summaries, signatures) = Self::episode_dependencies(conn, obligation_id)?;
                Ok(signatures.join("\n"))
            }
            ObservationField::Diagnostics => {
                Ok(Self::episode_latest_diagnostic(conn, episode_id)?.unwrap_or_default())
            }
            ObservationField::ProofHistory => {
                let lesson: Option<String> = conn.query_row(
                    "SELECT failure_lesson FROM episode_obligations WHERE id = ?1 AND episode_id = ?2",
                    [obligation_id.to_string(), episode_id.to_string()],
                    |row| row.get(0),
                ).optional().map_err(|e| e.to_string())?.flatten();
                Ok(lesson.unwrap_or_default())
            }
        }
    }

    pub fn build(
        &self,
        conn: &Connection,
        obligation: &Obligation,
        environment_hash: &str,
        root_formal_statement: &str,
    ) -> Result<CompactContext, String> {
        let obligation_signature = format!(
            "theorem {} : {}",
            obligation.theorem_name, obligation.lean_statement
        );

        // Fetch direct dependencies
        let mut stmt = conn.prepare(
            "SELECT dependency_obligation_id FROM obligation_edges WHERE parent_obligation_id = ?1"
        ).map_err(|e| e.to_string())?;

        let dep_ids = stmt
            .query_map([obligation.id.to_string()], |row| row.get::<_, String>(0))
            .map_err(|e| e.to_string())?;

        let mut dependency_summaries = Vec::new();
        let mut dependency_full_signatures = Vec::new();
        for id_res in dep_ids {
            let id_str = id_res.map_err(|e| e.to_string())?;
            let mut o_stmt = conn.prepare(
                "SELECT theorem_name, lean_statement, statement_hash, status FROM obligations WHERE id = ?1"
            ).map_err(|e| e.to_string())?;

            let (name, stmt_text, stmt_hash, status) = o_stmt
                .query_row([id_str.clone()], |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, String>(1)?,
                        row.get::<_, String>(2)?,
                        row.get::<_, String>(3)?,
                    ))
                })
                .map_err(|e| e.to_string())?;

            if status != "proved" {
                return Err(format!(
                    "Invariant violation: direct dependency {} is not proved (status={})",
                    id_str, status
                ));
            }

            dependency_summaries.push(DependencySummary {
                theorem_name: name.clone(),
                status,
                statement_hash: stmt_hash,
            });
            dependency_full_signatures.push(format!("theorem {} : {}", name, stmt_text));
        }

        // Fetch latest diagnostic
        let mut attempt_stmt = conn
            .prepare(
                "SELECT diagnostic_json FROM proposal_attempts
             WHERE obligation_id = ?1 AND outcome IN ('kernel_fail', 'timeout')
             ORDER BY created_at DESC LIMIT 1",
            )
            .map_err(|e| e.to_string())?;

        let latest_diagnostic: Option<String> = attempt_stmt
            .query_row([obligation.id.to_string()], |row| row.get(0))
            .optional()
            .map_err(|e| e.to_string())?
            .flatten();

        let raw = RawObservation {
            env_id: environment_hash.to_string(),
            import_manifest_hash: String::new(), // legacy canonical-storage path predates manifests; unused by MCP
            obligation_signature,
            obligation_statement_hash: obligation.statement_hash.clone(),
            root_theorem_signature: root_formal_statement.to_string(),
            dependency_summaries,
            dependency_full_signatures,
            latest_diagnostic,
            distilled_lesson: obligation.failure_lesson.clone(),
            retrieved_hint: None,
        };

        Ok(self.assemble(raw))
    }
}

#[cfg(test)]
mod budget_tests {
    use super::*;

    fn raw(
        root: &str,
        deps: Vec<&str>,
        diagnostic: Option<&str>,
        lesson: Option<&str>,
    ) -> RawObservation {
        RawObservation {
            env_id: "env".to_string(),
            import_manifest_hash: "manifest".to_string(),
            obligation_signature: "theorem O : True".to_string(),
            obligation_statement_hash: "obl_hash".to_string(),
            root_theorem_signature: root.to_string(),
            dependency_summaries: deps
                .iter()
                .enumerate()
                .map(|(i, _)| DependencySummary {
                    theorem_name: format!("dep{}", i),
                    status: "proved".to_string(),
                    statement_hash: format!("h{}", i),
                })
                .collect(),
            dependency_full_signatures: deps.iter().map(|s| s.to_string()).collect(),
            latest_diagnostic: diagnostic.map(|s| s.to_string()),
            distilled_lesson: lesson.map(|s| s.to_string()),
            retrieved_hint: None,
        }
    }

    #[test]
    fn small_observation_inlines_everything_with_no_references() {
        let builder = CompactContextBuilder::new(1000);
        let ctx = builder.assemble(raw(
            "theorem root : 1 + 1 = 2",
            vec!["theorem a : True", "theorem b : True"],
            Some("{\"error\":\"oops\"}"),
            Some("try induction"),
        ));
        assert!(ctx.references.is_empty());
        assert!(!ctx.budget.truncated);
        assert_eq!(ctx.budget.omitted_bytes, 0);
        assert_eq!(ctx.budget.referenced_bytes, 0);
        assert_eq!(ctx.root_theorem_signature, "theorem root : 1 + 1 = 2");
        assert_eq!(ctx.direct_dependency_signatures.len(), 2);
        assert_eq!(ctx.direct_dependencies.len(), 2);
        assert_eq!(
            ctx.latest_diagnostic.as_deref(),
            Some("{\"error\":\"oops\"}")
        );
    }

    #[test]
    fn never_returns_context_too_large_for_huge_root() {
        // Tiny budget, enormous root statement.
        let builder = CompactContextBuilder::with_bytes_per_token(8, 4); // 32-byte ceiling
        let huge_root = "x".repeat(100_000);
        let ctx = builder.assemble(raw(&huge_root, vec![], None, None));
        // Core (obligation + hashes) is always present; root is referenced.
        assert!(ctx.budget.truncated);
        let root_ref = ctx
            .references
            .iter()
            .find(|r| r.field == ObservationField::RootTheorem)
            .expect("root theorem must be referenced when omitted");
        assert_eq!(root_ref.total_bytes, 100_000);
        assert!(root_ref.included_bytes < 100_000);
        assert_eq!(root_ref.next_offset, root_ref.included_bytes);
        // Included prefix matches what the reference claims.
        assert_eq!(ctx.root_theorem_signature.len(), root_ref.included_bytes);
        // Accounting: omitted + included prefix == total referenced.
        assert_eq!(ctx.budget.omitted_bytes, 100_000 - root_ref.included_bytes);
        assert_eq!(ctx.budget.referenced_bytes, 100_000);
    }

    #[test]
    fn large_diagnostic_keeps_guaranteed_head_even_when_budget_exhausted() {
        // Budget consumed by a large root; diagnostic still gets its head.
        let builder = CompactContextBuilder::with_bytes_per_token(4, 4); // 16-byte ceiling
        let big_root = "r".repeat(10_000);
        let big_diag = "d".repeat(10_000);
        let ctx = builder.assemble(raw(&big_root, vec![], Some(&big_diag), None));
        let head = ctx
            .latest_diagnostic
            .expect("diagnostic head always present");
        assert_eq!(head.len(), DIAGNOSTIC_HEAD_BYTES.min(10_000));
        let diag_ref = ctx
            .references
            .iter()
            .find(|r| r.field == ObservationField::Diagnostics)
            .expect("diagnostic must be referenced when only the head is inlined");
        assert_eq!(diag_ref.included_bytes, DIAGNOSTIC_HEAD_BYTES);
        assert_eq!(diag_ref.total_bytes, 10_000);
    }

    #[test]
    fn dozens_of_dependencies_are_summarized_and_referenced() {
        let builder = CompactContextBuilder::with_bytes_per_token(20, 4); // 80-byte ceiling
        let deps: Vec<String> = (0..60)
            .map(|i| format!("theorem d{} : some_long_statement_{}", i, i))
            .collect();
        let dep_refs: Vec<&str> = deps.iter().map(|s| s.as_str()).collect();
        let ctx = builder.assemble(raw("theorem root : True", dep_refs, None, None));
        // Every dependency is summarized (name+status+hash) regardless of budget.
        assert_eq!(ctx.direct_dependencies.len(), 60);
        // Not all full signatures fit; the remainder is referenced.
        assert!(ctx.direct_dependency_signatures.len() < 60);
        assert!(ctx
            .references
            .iter()
            .any(|r| r.field == ObservationField::DependencySignatures));
    }

    #[test]
    fn char_boundary_prefix_is_valid_utf8() {
        let builder = CompactContextBuilder::with_bytes_per_token(2, 4); // 8-byte ceiling
                                                                         // Multi-byte characters near the truncation point.
        let root = "αβγδεζηθ".to_string(); // each 2 bytes
        let ctx = builder.assemble(raw(&root, vec![], None, None));
        // The inlined prefix must be valid UTF-8 (no panic on to_string / str slice).
        assert!(ctx
            .root_theorem_signature
            .chars()
            .all(|c| "αβγδεζηθ".contains(c)));
    }
}

#[cfg(all(test, feature = "legacy_tests"))]
mod tests {
    use super::*;
    use crate::db::{initialize_db, insert_obligation, insert_problem_version};
    use crate::models::{
        FidelityStatus, ObligationCreator, ObligationKind, ObligationStatus, ProblemState,
        ProblemVersion,
    };
    use chrono::Utc;

    #[test]
    fn test_context_builder_success() {
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

        let builder = CompactContextBuilder::new(1000);
        let ctx = builder
            .build(
                &conn,
                &o_root,
                "envhash",
                "theorem root (x : Int) : x + 0 = x",
            )
            .unwrap();
        assert_eq!(ctx.env_id, "envhash");
        assert_eq!(
            ctx.root_theorem_signature,
            "theorem root (x : Int) : x + 0 = x"
        );
        assert_eq!(ctx.obligation_signature, "theorem O_root : x + 0 = x");
        assert!(ctx.direct_dependency_signatures.is_empty());
    }
}
