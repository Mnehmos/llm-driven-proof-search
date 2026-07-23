# External dependency provenance

## external_Hadamard_Proof (removed gitlink, PR #265 review blocker 1)

Earlier exploratory phases of this campaign consulted a prior external Hadamard
search repository. It was accidentally committed as a bare gitlink with no
`.gitmodules`, which a fresh clone cannot resolve; the gitlink is removed and
the dependency is recorded here as provenance instead:

- Repository: https://github.com/renaissancefieldlite/Hadamard_Proof
- Commit consulted: `6e4a8cc5f61abf081596b3dd9df17a5619ea1ce2` ("Publish staged guard-cap seed shaping rung")
- Role: exploratory prior art only (earlier heuristic search protocols and
  notes). No decisive verdict, certificate, or committed artifact in this
  campaign depends on code from that repository; the decisive tool-chain is
  fully contained in this directory.
- The local working copy is ignored via .gitignore.
