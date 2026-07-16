# Erdős #647 dossiers

This directory contains the proof-search provenance layer for the campaign.

- [exports/](exports/README.md): complete 328-episode archive in public-summary,
  full Markdown, and structured training formats.
- [episode-index.tsv](episode-index.tsv): compact problem/episode lookup index,
  now extended from the original 104 modular rows to all 328 related episodes.
- [public-summaries.md](public-summaries.md): preserved legacy bundle for the
  original eight headline episodes.
- [tools/](tools/README.md): reproducible fixed-depth search sources, clearly
  separated from the kernel-verified witness the search helped locate.

The exports are audit metadata and proof-search history. The portable formal
artifact remains the committed Lean source under [../proof/](../proof/).

The final global density theorem is a repository-level composition replayed
from its full transitive source graph. It is documented in
[../evidence.md](../evidence.md) and is intentionally not fabricated as an
extra proof-search episode.

The newest tracked episodes cover exact fixed-depth consistency witnesses,
the shift-13/14/15 refinements, the generic shift-factor and next-adic-lift
framework, the exact eventual-excess interface for the limit variant, and the
first infinite-window frontier. The archive now contains 321 kernel-verified
successes and seven retained non-success histories. Source-composed converses
and frontier assemblies—including shift 16, which has a source replay and an
independent `kernel_pass` but no tracked episode—are documented as repository
replays rather than invented episode records.
