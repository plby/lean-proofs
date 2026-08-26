import ErdosProblems.Erdos336.MinimalHighOrderFourier
import ErdosProblems.Erdos336.FourierPartialRectification

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- The precise partial-rectification output supplied by the corrected Fourier
argument: over four fifths of the set lies in a progression of quotient fibres
whose span is strictly less than half the quotient. -/
def PartialRectificationCertificate (A : Finset (ZMod N)) : Prop :=
  ∃ (m : ℕ) (hm : 0 < m),
    let _ : NeZero m := ⟨hm.ne'⟩
    ∃ (π : ZMod N →+ ZMod m), Function.Surjective π ∧ 37 ≤ m ∧
      ∃ B : Finset (ZMod N), B ⊆ A ∧ 4 * A.card < 5 * B.card ∧
        ∃ α : ZMod m, ∀ x ∈ B,
          ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m)

/-- Every minimal V3 counterexample at a large power has the explicit partial
rectification certificate. -/
theorem minimalV3_counterexample_partial_rectification
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
    PartialRectificationCertificate (exactPowerFinset C t) := by
  let A : Finset (ZMod N) := exactPowerFinset C t
  obtain ⟨k, hkorder, hhalf⟩ :=
    minimalV3_counterexample_high_order_fourier_four_fifths
      C t ht hzero hprimitive hdoub hnot hsmaller
  have hk : k ≠ 0 := by
    intro hk0
    subst k
    simp at hkorder
  have hhalfSub : fourierPositiveHalf A k ⊆ A :=
    Finset.filter_subset _ _
  have hhalfCard : (fourierPositiveHalf A k).card ≤ A.card :=
    Finset.card_le_card hhalfSub
  have hF : cyclicFinsetFourier A k ≠ 0 := by
    intro hzeroF
    have hempty : fourierPositiveHalf A k = ∅ := by
      ext x
      simp [fourierPositiveHalf, hzeroF]
    rw [hempty] at hhalf
    simp at hhalf
  obtain ⟨m, hm, π, hπ, hmorder, α, hα⟩ :=
    positiveHalf_short_quotient_interval A k hk hF
  letI : NeZero m := ⟨hm.ne'⟩
  refine ⟨m, hm, π, hπ, ?_, fourierPositiveHalf A k, ?_, hhalf, α, ?_⟩
  · rw [hmorder]
    omega
  · exact Finset.filter_subset _ _
  · intro x hx
    exact hα x hx

end Erdos336
