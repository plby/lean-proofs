import ErdosProblems.Erdos336.MinimalHighOrderFourierCoefficient
import ErdosProblems.Erdos336.FourierNineTenthsPartialRectification

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {N : ℕ} [NeZero N]

/-- More than nine tenths of the set lies over a sub-half cyclic interval in
an exact frequency quotient of order at least 37. -/
def NineTenthsPartialRectificationCertificate
    (A : Finset (ZMod N)) : Prop :=
  ∃ (m : ℕ) (hm : 0 < m),
    let _ : NeZero m := ⟨hm.ne'⟩
    ∃ (π : ZMod N →+ ZMod m), Function.Surjective π ∧ 37 ≤ m ∧
      ∃ B : Finset (ZMod N), B ⊆ A ∧ 9 * A.card < 10 * B.card ∧
        ∃ α : ZMod m, ∀ x ∈ B,
          ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m)

/-- Freiman's semicircle integral upgrades the minimal-counterexample Fourier
coefficient from a four-fifths open half-plane slice to a nine-tenths
half-open slice, without weakening the strict sub-half quotient span. -/
theorem minimalV3_counterexample_nine_tenths_partial_rectification
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
    NineTenthsPartialRectificationCertificate (exactPowerFinset C t) := by
  let A : Finset (ZMod N) := exactPowerFinset C t
  obtain ⟨k, hkorder, hkcoeff⟩ :=
    minimalV3_counterexample_high_order_fourier_coefficient
      C t ht hzero hprimitive hdoub hnot hsmaller
  have hk : k ≠ 0 := by
    intro hk0
    subst k
    simp at hkorder
  have hnorm : 0 ≤ ‖cyclicFinsetFourier A k‖ := norm_nonneg _
  have hcard : 0 ≤ (A.card : ℝ) := by positivity
  have hlarge : 4 * (A.card : ℝ) <
      5 * ‖cyclicFinsetFourier A k‖ := by
    change 16 * (A.card : ℝ) ^ 2 <
      25 * ‖cyclicFinsetFourier A k‖ ^ 2 at hkcoeff
    nlinarith
  have hF : cyclicFinsetFourier A k ≠ 0 := by
    intro hF0
    rw [hF0, norm_zero] at hlarge
    have hnonneg : 0 ≤ 4 * (A.card : ℝ) := by positivity
    linarith
  obtain ⟨m, hm, π, hπ, hmorder, B, hBA, hdense, α, hα⟩ :=
    fourier_nine_tenths_short_quotient_interval A k hk hF hlarge
  letI : NeZero m := ⟨hm.ne'⟩
  refine ⟨m, hm, π, hπ, ?_, B, ?_, ?_, α, ?_⟩
  · rw [hmorder]
    omega
  · simpa [A] using hBA
  · simpa [A] using hdense
  · intro x hx
    exact hα x hx

end Erdos336
