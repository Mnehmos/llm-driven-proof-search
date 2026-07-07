# Disclosure note — why full proof bodies and traces are published here

The proof-search environment gates full-body exports of benchmark-linked
episodes behind an explicit flag (`allow_putnambench_proof_export`), because
for held-out competition corpora (PutnamBench) publishing completed proofs
contaminates the benchmark. That flag was set `true` for the exports in this
folder. The justification, recorded for the audit trail:

1. **These proofs are the contribution, not a leak.** The Erdős corpus
   (erdosproblems.com / google-deepmind/formal-conjectures) *solicits*
   public formal proofs — its own `@[formal_proof using … at "<url>"]`
   mechanism exists to link externally hosted proofs. Publishing is the
   intended endpoint, decided deliberately, not a side channel.
2. **No held-out answers exist.** These are research problems and their
   solved variants, not competition items with secret solutions.
3. **The redaction machinery still did its job**: `public_summary` exports
   remain redacted (`proof_body_redacted: true`), and the flag left an
   explicit, auditable record that disclosure was a choice.

Tracked-benchmark proof bodies from PutnamBench remain unpublished and are
NOT in this folder.
