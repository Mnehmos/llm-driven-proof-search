# Erdős #647 — legacy headline public summaries

> These records were produced by the proof-search environment's `proof_export`
> tool in `public_summary` mode — a redacted, public-safe export that carries
> the kernel-verification status, root statement, environment/import-manifest
> hashes, and trajectory integrity hashes, but **never** the proof body.
> This file preserves the original eight-headline bundle generated
> 2026-07-13. The complete 211-episode archive updated 2026-07-15 is in
> [exports/](exports/README.md), with one public summary, full Markdown
> dossier, and structured training export per episode. It contains 204
> kernel-verified successes and seven retained non-success histories. Each is
> independently reproducible: given the
> `episode_id`, re-run `proof_export{episode_id, format: "public_summary"}`
> against the pinned environment (`environment_hash` below) and compare.
>
> The eight records below are the original headline theorems (Theorem 2's
> three stages + the five
> Layer-A quantitative-Mertens infrastructure lemmas). Full proof snapshots
> for these live in [../proof/](../proof/). The current theorem inventory is
> in [../THEOREM-CATALOG.md](../THEOREM-CATALOG.md).

Common to all records below:
- `environment_hash`: `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- `import_manifest_hash`: `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- `outcome`: `KERNEL_VERIFIED`, `kernel_verified: true`, `fidelity_status: attested`, `proof_body_redacted: true`

---

## Theorem 2 (prime-chain reduction) — stage k = 1,2

- **episode_id**: `c4a688c1-053c-4e08-8da3-e3ab7c4c594e`
- **root_formal_statement**: `∀ n : ℕ, 24 < n → ArithmeticFunction.sigma 0 (n - 1) ≤ 3 → ArithmeticFunction.sigma 0 (n - 2) ≤ 4 → ∃ q : ℕ, Nat.Prime q ∧ n = 2 * q + 2 ∧ Nat.Prime (n - 1)`
- **trajectory_first_hash**: `dd1efecae7abe1c5167ca65ea3970879650fc1c521613dd02b5dd19a4f7440b3`
- **trajectory_last_hash**: `8e588b5d6c0dd632e437757019a2fb578736cc96ff374be6dff88b934358f9ab`

## Theorem 2 — stage k = 4

- **episode_id**: `57bf2fb3-7a57-4644-b99a-f97ff2aa600c`
- **root_formal_statement**: `∀ q : ℕ, 13 ≤ q → q.Prime → (2*q+1).Prime → ArithmeticFunction.sigma 0 (2*q - 2) ≤ 6 → ∃ p : ℕ, p.Prime ∧ q = 2*p+1`
- **trajectory_first_hash**: `1f1b857c4f3c89a20d1cf4de87f336b56f05cc37ce9eae48daf44dc510c6ac92`
- **trajectory_last_hash**: `d83e7c401bc235319499924be561432776cd4526c7a45fe593a2243c307da91d`

## Theorem 2 — stage k = 8 (final family split)

- **episode_id**: `95fae0a4-f448-4236-9039-604e5cb902e7`
- **root_formal_statement**: `∀ p : ℕ, 7 ≤ p → p.Prime → (2*p+1).Prime → ArithmeticFunction.sigma 0 (4*p - 4) ≤ 10 → ∃ s : ℕ, s.Prime ∧ (p = 2*s+1 ∨ p = 4*s+1)`
- **trajectory_first_hash**: `2a134f9604d0edfeed67d28f1df12792b93fe06f1c22aa4e01b1ee9d7b0ff58e`
- **trajectory_last_hash**: `af2edab1dc0968878c9364bc157a019433118d56e915693f60bd2051ece85eaf`

## Layer A — exact Mertens identity via Chebyshev θ

- **episode_id**: `7a7e8098-a5bf-4dd9-97df-145e34ee914b`
- **root_formal_statement**: `∀ x : ℝ, 2 ≤ x → ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1/(p:ℝ)) = Chebyshev.theta x / (x * Real.log x) + ∫ t in Set.Ioc (2:ℝ) x, (Real.log t + 1) / (t^2 * (Real.log t)^2) * Chebyshev.theta t`
- **trajectory_first_hash**: `6170be55d80001f00c19dfe98869045f17814af4b3353486dda602fc9332e934`
- **trajectory_last_hash**: `59321865519c8c15c86e3596e6f7612c07d1469d9a4bc76df77cc7484e72e9b2`

## Layer A — main-term antiderivative

- **episode_id**: `36f8eaa9-7116-44a3-b633-f8f1a03210f4`
- **root_formal_statement**: `∀ x : ℝ, 2 ≤ x → ∫ t in (2:ℝ)..x, (Real.log t + 1) / (t * (Real.log t)^2) = (Real.log (Real.log x) - (Real.log x)⁻¹) - (Real.log (Real.log 2) - (Real.log 2)⁻¹)`
- **trajectory_first_hash**: `622b8cf42d800646b7004714cd5d21a28ff271f3a61e76e273bd7a22c8347031`
- **trajectory_last_hash**: `4964c0534375f7d11d0239567b296f3cae54451a9fcf9d9216b0715554a101da`

## Layer A — Mertens weight integral

- **episode_id**: `700f297f-d8bc-448f-b118-2921e1b98491`
- **root_formal_statement**: `∀ x : ℝ, 2 ≤ x → ∫ t in (2:ℝ)..x, (Real.log t + 1) / (t^2 * (Real.log t)^2) = (2 * Real.log 2)⁻¹ - (x * Real.log x)⁻¹`
- **trajectory_first_hash**: `8dec105310a73993e8e12471a738605a632a7b9a01e58f0b27608e50bf057f50`
- **trajectory_last_hash**: `563239e248c18e9e600edcda11d09c1e238be3b12193b86a4c64cc5b2e6bbb01`

## Layer A — power-law comparison antiderivative

- **episode_id**: `1f97aff1-1173-4246-b6dd-06d15ff25ee4`
- **root_formal_statement**: `∀ x : ℝ, 2 ≤ x → ∫ t in (2:ℝ)..x, ((t^2)⁻¹) = (2:ℝ)⁻¹ - x⁻¹`
- **trajectory_first_hash**: `5e4e3ed47d7f6161d1df416a1f6423b16f116cfbbc0a2a2cc50bcdb613df5aa6`
- **trajectory_last_hash**: `51ff4c9fbc2c610887a4dae0a52709eeab593a2f6d7886dd756d3b07e579b40b`

## Layer A — log(t+2) error integral bound (first analytic inequality)

- **episode_id**: `6fa25185-251b-4203-a843-63fc2b0c43e6`
- **root_formal_statement**: `∀ x : ℝ, 2 ≤ x → (∫ t in (2:ℝ)..x, (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2)) ≤ 1 + (Real.log 2)⁻¹`
- **trajectory_first_hash**: `96a3e36fc8c8c7ae566df136461126d19b4e130472c3ff4059239c0503ca8fc1`
- **trajectory_last_hash**: `bdf33b8acdbe50d36de37d7958e6e7229178c2af92c7d8a0408f7b3c6c634520`
