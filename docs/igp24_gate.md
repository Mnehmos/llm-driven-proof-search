# IGP24 Gate

Use `scripts/igp24_gate.py` to prevent wasting SAIR IGP24 submission slots on
already-covered or baseline pairs. The gate requires every row to carry an
expected `(24Tt, r)`; do not bulk-submit untargeted random polynomials.

## Input

CSV is the simplest format:

```csv
label,r,polynomial,source,poly_disc_abs
24T293,16,"1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1","construction note",123
```

Accepted label columns: `label`, `expected_label`, `t`, `expected_t`, `24Tt`.
Accepted polynomial columns: `polynomial`, `coefficients`, `coeffs`.

Optional discriminant columns such as `nfdisc_abs`, `field_disc_abs`,
`scoring_disc_abs`, `poly_disc_abs`, or `disc_abs` are used only to choose the
best row when several candidates target the same expected pair.

## Dry Run

Set the API key in the process environment. Do not commit it to the repo.

```powershell
$env:SAIR_API_KEY = "..."
python scripts/igp24_gate.py data/igp24/candidates.csv `
  --output igp24/filtered_submission.txt `
  --report igp24/gate_report.json
```

Default behavior:

- skips invalid IGP24 coefficient lines,
- skips pairs that already have a participant discovery,
- skips LMFDB baseline pairs,
- skips pairs already seen in this team's submissions,
- keeps only one row per expected `(24Tt, r)`,
- sorts rare real-root signatures first.

For targeted competition batches, add stricter policy flags:

```powershell
python scripts/igp24_gate.py data/igp24/candidates.csv `
  --uncovered-labels-only `
  --min-r 18 `
  --max-polynomials 100 `
  --output igp24/filtered_targeted_submission.txt `
  --report igp24/filtered_targeted_report.json
```

Use `--max-label-team-count N` instead of `--uncovered-labels-only` when a
batch intentionally targets low-coverage labels rather than completely
uncovered labels. Use `--max-signature-team-count N` only when allowing
already-discovered signatures for discriminant-improvement experiments.

Generated files are ignored by git under `igp24/` and `data/igp24/`.

## Submit

Review `igp24/gate_report.json` first. Then:

```powershell
python scripts/igp24_gate.py data/igp24/candidates.csv --submit
```

Add `--yes` only for unattended runs after you trust the candidate source.

Baseline pairs are excluded by default. Use `--include-baseline` only when the
candidate has exact `nfdisc` evidence for a strict baseline improvement.

## Discovery Batches

Use `scripts/igp24_generate_batch.py` only for broad discovery/calibration
batches where the expected `24Tt` label is not known locally:

```powershell
python scripts/igp24_generate_batch.py --count 1000 --root-count-mode none `
  --output igp24/discovery_batch.txt `
  --manifest igp24/discovery_manifest.json
python scripts/igp24_submit.py igp24/discovery_batch.txt --dry-run
```

The generator uses local coefficient checks plus a modular irreducibility
filter. Passing that filter proves irreducibility over `Q`, but it does not
predict whether the pair is new or scoreable. Submit broad discovery batches
sparingly; once a family is seen to land in crowded public labels, switch to
labeled candidate sources and the gate above.

To submit a validated coefficient-only batch through the API:

```powershell
$env:SAIR_API_KEY = "..."
python scripts/igp24_submit.py igp24/discovery_batch.txt --yes `
  --description "Short provenance/reproduction note"
```

Poll and save the API state:

```powershell
python scripts/igp24_poll.py --output igp24/poll_latest.json
```

List currently open targets from the live progress endpoint:

```powershell
python scripts/igp24_targets.py `
  --output igp24/open_targets.csv `
  --summary igp24/open_targets_summary.json
```

For the next small discovery cycle, write a hard-first shortlist:

```powershell
python scripts/igp24_targets.py `
  --uncovered-labels-only `
  --exclude-baseline `
  --min-r 18 `
  --priority rare-r `
  --limit 100 `
  --output igp24/targets_uncovered_rare_high_r_100.csv `
  --summary igp24/targets_uncovered_rare_high_r_100_summary.json
```

Use this list to drive candidate sourcing. Rows with `label_team_count = 0`
are labels no team has publicly covered yet; those are better next targets
than another broad sparse-polynomial batch.

## Candidate Sources

Normalize public labeled sources into gate-compatible CSV before submitting.
LMFDB number-field rows can be fetched with:

```powershell
python scripts/igp24_source_lmfdb.py `
  --output data/igp24/lmfdb_degree24_candidates.csv `
  --report data/igp24/lmfdb_degree24_candidates_report.json
```

As of the current run, the strict gate selected zero LMFDB degree-24 rows for
high-r uncovered targets because those rows are baseline/crowded. Keep the
artifact as a negative control and provenance source, not as a submission batch.

The Mueller M24 family source emits expected `24T24680` candidates:

```powershell
python scripts/igp24_source_m24_muller.py `
  --t-min -25 `
  --t-max 25 `
  --output data/igp24/m24_muller_candidates.csv `
  --report data/igp24/m24_muller_candidates_report.json
```

This is a low-coverage/improvement source, not an uncovered-label source,
because `24T24680` already has public team coverage. The displayed
sum-of-squares specialization is also generically `r=0` over the reals, so use
it mainly as a Magma-label smoke test unless the target is an open `r=0`
improvement.

For the first high-confidence uncovered `r=24` target, use a cyclic
cyclotomic period:

```powershell
python scripts/igp24_source_cyclotomic_period.py `
  --output data/igp24/cyclotomic_period_candidates.csv `
  --report data/igp24/cyclotomic_period_candidates_report.json
```

The default conductor `97` construction produces a locally irreducible, totally
real degree-24 polynomial with expected label `24T1` (`C24`). Verify with Magma
when available, then submit the coefficient-only row from
`igp24/cyclotomic_period_24T1_submission.txt`.

For unlabeled high-real-root discovery, use quadratic lifts of totally real
degree-12 LMFDB fields:

```powershell
python scripts/igp24_generate_quadratic_lifts.py `
  --skip 0 `
  --limit 25 `
  --output igp24/quadratic_lift_r24_batch.txt `
  --manifest igp24/quadratic_lift_r24_manifest.json
```

Each row has the form `f(x^2 - M)` with `f` a totally real degree-12 source
polynomial. The script checks local irreducibility and exactly 24 real roots.
Use `--skip` for non-overlapping slices after a successful batch.

## Magma Verification

When Magma is available, verify source labels before the SAIR gate:

```powershell
$env:MAGMA_BIN = "C:\path\to\magma.exe"
python scripts/igp24_magma_verify.py data/igp24/source_candidates.csv `
  --run-galois-proof `
  --output data/igp24/source_magma_verified.csv `
  --report igp24/source_magma_verify_report.json
```

For a fast first pass, omit `--run-galois-proof`. For a stricter pass, add
`--require-proof`; this keeps only rows for which Magma's `GaloisProof`
succeeds. If Magma is not on `PATH`, the script still writes the `.m` batch file
so it can be run after `MAGMA_BIN` is configured.

Then gate the Magma-verified rows:

```powershell
python scripts/igp24_gate.py data/igp24/source_magma_verified.csv `
  --uncovered-labels-only `
  --min-r 18 `
  --output igp24/source_filtered_submission.txt `
  --report igp24/source_filtered_report.json
```
