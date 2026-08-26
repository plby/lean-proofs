import ErdosProblems.Erdos336.FourierHalfPlane
import ErdosProblems.Erdos336.StableHighPowerCertificateV2

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

private theorem zero_mem_power {C : Set (ZMod N)} (hzero : 0 ∈ C) (t : ℕ) :
    0 ∈ ExactPower C t := by
  refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
  intro y hy
  rw [List.mem_replicate] at hy
  simpa [hy.2] using hzero

lemma stableWeight_eq_double_sub_one
    {S : Set (ZMod N)} (hz : 0 ∈ S) :
    stableWeight S = (ExactPower S 2).ncard - 1 := by
  have hsub : S ⊆ ExactPower S 2 := by
    intro x hx
    rw [exactPower_eq_nsmul, two_nsmul]
    exact ⟨x, hx, 0, hz, by simp⟩
  have hle : S.ncard ≤ (ExactPower S 2).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hpos : 0 < S.ncard := by
    rw [Set.ncard_pos]
    exact ⟨0, hz⟩
  unfold stableWeight
  omega

/-- The Fourier step now needed from a high-power minimal counterexample:
full subset expansion plus failure of V2 automatically supply all hypotheses
of the corrected four-fifths theorem. -/
theorem highPower_counterexample_fourier_half
    (C : Set (ZMod N)) (t : ℕ) (ht : 61 ≤ t)
    (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hnot : ¬ StableHighPowerCertificateV2 C t)
    (hexpand : ∀ B : Finset (ZMod N),
      B ⊆ exactPowerFinset C t → 2 ≤ B.card →
      (exactPowerFinset C t).card + B.card ≤
        (exactPowerFinset C t + B).card) :
    ∃ k : ZMod N, k ≠ 0 ∧
      4 * (exactPowerFinset C t).card <
        5 * (fourierPositiveHalf (exactPowerFinset C t) k).card := by
  let S : Set (ZMod N) := ExactPower C t
  let A : Finset (ZMod N) := exactPowerFinset C t
  have hnotfull : S ≠ Set.univ := by
    intro hfull
    apply hnot
    change Fintype.card (ZMod N) = 1 ∨
      Fintype.card (ZMod N) < 12000 * stableWeight S ∨
      RankExceptionalCertificate S
    by_cases hN1 : N = 1
    · left; simpa using hN1
    · right; left
      have hNpos : 0 < N := NeZero.pos N
      have hN2 : 2 ≤ N := by omega
      have hU2 : ExactPower (Set.univ : Set (ZMod N)) 2 = Set.univ := by
        rw [exactPower_eq_nsmul, two_nsmul]
        simp
      rw [ZMod.card]
      unfold stableWeight
      rw [hfull, hU2]
      have hcardU : (Set.univ : Set (ZMod N)).ncard = N := by
        simp [Nat.card_eq_fintype_card]
      rw [hcardU]
      omega
  have hcardSet := add_one_le_ncard_exactPower_of_not_full
    hzero hprimitive t hnotfull
  have hcard : 62 ≤ A.card := by
    rw [card_exactPowerFinset]
    change 62 ≤ (ExactPower C t).ncard
    omega
  have hzS : 0 ∈ S := zero_mem_power hzero t
  have hweight := stableWeight_eq_double_sub_one hzS
  have hsparseSet : 12000 * ((ExactPower S 2).ncard - 1) ≤ N := by
    have hnotDense : ¬ Fintype.card (ZMod N) < 12000 * stableWeight S := by
      intro hdense
      exact hnot (Or.inr (Or.inl hdense))
    rw [ZMod.card] at hnotDense
    rw [hweight] at hnotDense
    omega
  have hsum : A + A = exactPowerFinset C (2 * t) := by
    apply Finset.coe_injective
    rw [Finset.coe_add]
    simp only [A, coe_exactPowerFinset]
    rw [exactPower_add]
    congr 2
    omega
  have hpower : ExactPower S 2 = ExactPower C (2 * t) := by
    simpa [S] using exactPower_exactPower C t 2
  have hdoubA : 4 * (A + A).card < 9 * A.card := by
    rw [hsum]
    simpa [A] using hdoub
  have hsparse : 12000 * ((A + A).card - 1) ≤ N := by
    rw [hsum, card_exactPowerFinset]
    rw [hpower] at hsparseSet
    exact hsparseSet
  obtain ⟨k, hk0, hk⟩ := exists_nonzero_fourier_gt_four_fifths A
    hcard hdoubA hsparse (by simpa [A] using hexpand)
  exact ⟨k, hk0, four_mul_card_lt_five_mul_positiveHalf A k hk⟩

end Erdos336
