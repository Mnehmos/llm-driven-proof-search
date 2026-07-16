import Mathlib

/-!
# Erdős #647 — candidate bridge with explicit additive range loss

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  20e17129-58dd-46aa-9a9f-d35e0d97c96b
  episode_id          48f49525-b5f1-4bac-8155-8dcfe91764ca
  root_statement_hash 091284a06deb6c14f157b9dbe555e00409b518e8bf9c274edfcb2a89f8ecb8e6
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    796c5543-2ead-471d-8219-d4438ab0e047 (kernel_pass)
  result_artifact_hash 2a35dad318e6a991c1b0161e19d6b2d96b51a4d0ae8a2e6ec381e4a4f4420264

This is the final set-theoretic candidate interface.  Parameters satisfying
`z < 157N` enter the exact coprime survivor count; the complementary band has
at most `z` elements.  Consequently the full bounded candidate Finset is
controlled by `siftedSum + z`.
-/

theorem erdos647_candidate_finset_le_siftedSum_add_z :
    ∀ (s : BoundingSieve) (X z : ℕ) (C : Finset ℕ),
      C ⊆ Finset.Icc 1 X →
      (∀ N ∈ C, z < 157*N →
        Nat.Coprime s.prodPrimes
          ((210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
            (840*N-1)*(1260*N-1)*(2520*N-1))) →
      s.siftedSum =
        (((Finset.Icc 1 X).filter (fun N =>
          Nat.Coprime s.prodPrimes
            ((210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
              (840*N-1)*(1260*N-1)*(2520*N-1)))).card : ℝ) →
      (C.card : ℝ) ≤ s.siftedSum + z := by
  intro s X z C hCX hcop hsift
  let G := C.filter (fun N => z < 157*N)
  let B := C.filter (fun N => 157*N ≤ z)
  have hGsub : G ⊆ (Finset.Icc 1 X).filter (fun N =>
      Nat.Coprime s.prodPrimes
        ((210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
          (840*N-1)*(1260*N-1)*(2520*N-1))) := by
    intro N hN
    simp only [G, Finset.mem_filter] at hN ⊢
    exact ⟨hCX hN.1, hcop N hN.1 hN.2⟩
  have hGcard : (G.card : ℝ) ≤ s.siftedSum := by
    rw [hsift]
    exact_mod_cast Finset.card_le_card hGsub
  have hBsub : B ⊆ Finset.Icc 1 z := by
    intro N hN
    simp only [B, Finset.mem_filter, Finset.mem_Icc] at hN ⊢
    have hNX := hCX hN.1
    simp only [Finset.mem_Icc] at hNX
    omega
  have hBcardNat : B.card ≤ z := by
    calc
      B.card ≤ (Finset.Icc 1 z).card := Finset.card_le_card hBsub
      _ = z := by rw [Nat.card_Icc]; omega
  have hBcard : (B.card : ℝ) ≤ z := by
    exact_mod_cast hBcardNat
  have hcover : C ⊆ G ∪ B := by
    intro N hN
    simp only [Finset.mem_union, G, B, Finset.mem_filter]
    by_cases hsmall : z < 157*N
    · exact Or.inl ⟨hN, hsmall⟩
    · exact Or.inr ⟨hN, by omega⟩
  have hcardNat : C.card ≤ G.card + B.card := by
    calc
      C.card ≤ (G ∪ B).card := Finset.card_le_card hcover
      _ ≤ G.card + B.card := Finset.card_union_le _ _
  have hcard : (C.card : ℝ) ≤ (G.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast hcardNat
  linarith
