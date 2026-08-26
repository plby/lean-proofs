import ErdosProblems.Erdos336.FourierHighOrder
import ErdosProblems.Erdos336.HighPowerFourierHalf
import ErdosProblems.Erdos336.MinimalAlmostExpansionV3

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- A minimal V2 counterexample already has enough expansion for a robust
Fourier concentration: no Kemperman/full-expansion input is needed. -/
theorem minimalV3_counterexample_high_order_fourier_coefficient
    (C : Set (ZMod N)) (t : ℕ) (ht : 237 ≤ t)
    (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hnot : ¬ StableHighPowerCertificateV3 C t)
    (hsmaller : ∀ (m : ℕ) (hm : 0 < m),
      let _ : NeZero m := ⟨hm.ne'⟩
      m < N →
        ∀ (D : Set (ZMod m)), 0 ∈ D →
          7 ≤ (ExactPower D t).ncard →
          (∃ q : ℕ, ExactPower D q = Set.univ) →
          4 * (ExactPower D (2 * t)).ncard <
            9 * (ExactPower D t).ncard →
          StableHighPowerCertificateV3 D t) :
    ∃ k : ZMod N, 36 < addOrderOf k ∧
      16 * ((exactPowerFinset C t).card : ℝ) ^ 2 <
        25 * ‖cyclicFinsetFourier (exactPowerFinset C t) k‖ ^ 2 := by
  let S : Set (ZMod N) := ExactPower C t
  let A : Finset (ZMod N) := exactPowerFinset C t
  have hnotfull : S ≠ Set.univ := by
    intro hfull
    apply hnot
    change Fintype.card (ZMod N) = 1 ∨
      Fintype.card (ZMod N) < (10000000 * Nat.factorial 36) * stableWeight S ∨
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
      simp only [Nat.sub_self, add_zero]
      have hK3 : 3 ≤ 10000000 * Nat.factorial 36 := by
        norm_num [Nat.factorial]
      have hmul := Nat.mul_le_mul_right (N - 1) hK3
      omega
  have hcardSet := add_one_le_ncard_exactPower_of_not_full
    hzero hprimitive t hnotfull
  have hcard : 238 ≤ A.card := by
    rw [card_exactPowerFinset]
    change 238 ≤ (ExactPower C t).ncard
    omega
  have hcardN : 7 ≤ (ExactPower C t).ncard := by
    have : 238 ≤ (ExactPower C t).ncard := by
      simpa [A, card_exactPowerFinset] using hcard
    omega
  have hNpos : 0 < N := NeZero.pos N
  have hFcard : Fintype.card (ZMod N) = N := ZMod.card N
  have hsmaller' : ∀ (m : ℕ) (hm : 0 < m),
      let _ : NeZero m := ⟨hm.ne'⟩
      m < Fintype.card (ZMod N) →
        ∀ (D : Set (ZMod m)), 0 ∈ D →
          7 ≤ (ExactPower D t).ncard →
          (∃ q : ℕ, ExactPower D q = Set.univ) →
          4 * (ExactPower D (2 * t)).ncard <
            9 * (ExactPower D t).ncard →
          StableHighPowerCertificateV3 D t := by
    simpa [hFcard] using hsmaller
  have halmost : ∀ B : Finset (ZMod N), B.Nonempty → B ⊆ A →
      A.card + B.card ≤ (A + B).card + 1 := by
    intro B hB hBsub
    simpa [A] using almost_expansion_of_smaller_stableV3
      C t (by omega) hzero hcardN hprimitive hdoub hnot hsmaller' hB hBsub
  have hzS : 0 ∈ S := by
    refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
    intro y hy
    rw [List.mem_replicate] at hy
    simpa [hy.2] using hzero
  have hweight := stableWeight_eq_double_sub_one hzS
  have hsparseSet : (10000000 * Nat.factorial 36) * ((ExactPower S 2).ncard - 1) ≤ N := by
    have hnotDense : ¬ Fintype.card (ZMod N) < (10000000 * Nat.factorial 36) * stableWeight S := by
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
  have hsparse : (10000000 * Nat.factorial 36) * ((A + A).card - 1) ≤ N := by
    rw [hsum, card_exactPowerFinset]
    rw [hpower] at hsparseSet
    exact hsparseSet
  obtain ⟨k, hk0, hk⟩ :=
    exists_high_order_fourier_gt_four_fifths A hcard hdoubA
      hsparse halmost
  exact ⟨k, hk0, by simpa [A] using hk⟩

end Erdos336
