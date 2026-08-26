import ErdosProblems.Erdos336.MinimalV3NineTenthsPartialRectification
import ErdosProblems.Erdos336.HighPowerTwoMinusOne
import ErdosProblems.Erdos336.MinimalAlmostExpansionV3

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- Partial rectification strengthened by the high-power covering relation
`A ⊆ 2B-B`. -/
def StrongNineTenthsPartialRectificationCertificate (A : Finset (ZMod N)) : Prop :=
  ∃ (m : ℕ) (hm : 0 < m),
    let _ : NeZero m := ⟨hm.ne'⟩
    ∃ (π : ZMod N →+ ZMod m), Function.Surjective π ∧ 37 ≤ m ∧
      ∃ B : Finset (ZMod N), B ⊆ A ∧ 9 * A.card < 10 * B.card ∧
        A ⊆ (B + B) - B ∧
        ∃ α : ZMod m, ∀ x ∈ B,
          ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m)

/-- A minimal V3 counterexample has a four-fifths rectified subset whose
`2B-B` already contains the whole high power. -/
theorem minimalV3_counterexample_strong_nine_tenths_partial_rectification
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
    StrongNineTenthsPartialRectificationCertificate (exactPowerFinset C t) := by
  let S : Set (ZMod N) := ExactPower C t
  let A : Finset (ZMod N) := exactPowerFinset C t
  obtain ⟨m, hm, π, hπ, hm37, B, hBA, hdenseB, α, hα⟩ :=
    minimalV3_counterexample_nine_tenths_partial_rectification
      C t ht hzero hprimitive hdoub hnot hsmaller
  letI : NeZero m := ⟨hm.ne'⟩
  have hnotfull : S ≠ Set.univ := by
    intro hfull
    apply hnot
    change Fintype.card (ZMod N) = 1 ∨
      Fintype.card (ZMod N) < (10000000 * Nat.factorial 36) * stableWeight S ∨
      RankExceptionalCertificate S
    by_cases hN1 : N = 1
    · left
      simpa using hN1
    · right
      left
      have hN2 : 2 ≤ N := by
        have hNpos : 0 < N := NeZero.pos N
        omega
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
  have hlarge := add_one_le_ncard_exactPower_of_not_full
    hzero hprimitive t hnotfull
  have hcard2 : 2 ≤ (ExactPower C t).ncard := by omega
  have hcard7 : 7 ≤ (ExactPower C t).ncard := by omega
  have hFcard : Fintype.card (ZMod N) = N := ZMod.card N
  have hsmaller' : ∀ (u : ℕ) (hu : 0 < u),
      let _ : NeZero u := ⟨hu.ne'⟩
      u < Fintype.card (ZMod N) →
        ∀ (D : Set (ZMod u)), 0 ∈ D →
          7 ≤ (ExactPower D t).ncard →
          (∃ q : ℕ, ExactPower D q = Set.univ) →
          4 * (ExactPower D (2 * t)).ncard <
            9 * (ExactPower D t).ncard →
          StableHighPowerCertificateV3 D t := by
    simpa [hFcard] using hsmaller
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos]
    simpa [A, card_exactPowerFinset] using
      (show 0 < (ExactPower C t).ncard by omega)
  have halmostSelf : A.card + A.card ≤ (A + A).card + 1 := by
    simpa [A] using almost_expansion_of_smaller_stableV3
      C t (by omega) hzero hcard7 hprimitive hdoub hnot hsmaller'
      hAne (by simpa [A])
  have hself : 2 * (ExactPower C t).ncard ≤
      (ExactPower C (2 * t)).ncard + 1 := by
    rw [← card_exactPowerFinset C t,
      ← card_exactPowerFinset C (2 * t), ← exactPowerFinset_add_self]
    simpa [A, two_mul] using halmostSelf
  have hdenseFour : 4 * (ExactPower C t).ncard < 5 * B.card := by
    have hdenseNine : 9 * (ExactPower C t).ncard < 10 * B.card := by
      simpa [card_exactPowerFinset] using hdenseB
    nlinarith
  have hcover : exactPowerFinset C t ⊆ (B + B) - B :=
    highPower_subset_two_sub_of_not_stableV3 C t (by omega)
      hzero hprimitive hnot hcard2 hdoub hself B hBA hdenseFour
  refine ⟨m, hm, π, hπ, hm37, B, hBA, hdenseB, hcover, α, hα⟩

end Erdos336
