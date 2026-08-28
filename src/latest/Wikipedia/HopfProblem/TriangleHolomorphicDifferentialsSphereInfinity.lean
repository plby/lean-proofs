import Mathlib.Analysis.Complex.Liouville

/-!
# Vanishing from an analytic inverse-coordinate germ

An inverse-coordinate formula with a positive power of `z⁻¹` forces a
function to tend to zero at infinity. If that function is entire,
Liouville's theorem makes it identically zero. The case of power two
is the scalar vanishing criterion for a holomorphic one-form on the
Riemann sphere.
-/

noncomputable section

open Filter
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsSphere

/-- A positive inverse-coordinate power times an analytic germ tends
to zero along the complement of compact sets. -/
theorem tendsto_zero_of_inverse_germ {F H : ℂ → ℂ} {m : ℕ}
    (hH : AnalyticAt ℂ H 0) (hm : 0 < m)
    (hinfty : F =ᶠ[cocompact ℂ] fun z => z⁻¹ ^ m * H z⁻¹) :
    Tendsto F (cocompact ℂ) (𝓝 0) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0 : ℂ)) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hlim : Tendsto (fun z : ℂ => z⁻¹ ^ m * H z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [zero_pow (Nat.ne_of_gt hm), zero_mul, Function.comp_apply] using
      (hi.pow m).mul (hH.continuousAt.tendsto.comp hi)
  exact hlim.congr' hinfty.symm

/-- An entire function represented at infinity by a positive inverse
power times an analytic germ vanishes everywhere. -/
theorem entire_eq_zero_of_inverse_germ {F H : ℂ → ℂ} {m : ℕ}
    (hF : ∀ z, AnalyticAt ℂ F z) (hH : AnalyticAt ℂ H 0) (hm : 0 < m)
    (hinfty : F =ᶠ[cocompact ℂ] fun z => z⁻¹ ^ m * H z⁻¹) (z : ℂ) : F z = 0 := by
  have hd : Differentiable ℂ F := fun w => (hF w).differentiableAt
  exact hd.apply_eq_of_tendsto_cocompact z (tendsto_zero_of_inverse_germ hH hm hinfty)

/-- The inverse-square transition of a holomorphic one-form forces
its entire affine coefficient to vanish. -/
theorem oneForm_eq_zero_of_inverse_germ {F H : ℂ → ℂ}
    (hF : ∀ z, AnalyticAt ℂ F z) (hH : AnalyticAt ℂ H 0)
    (hinfty : F =ᶠ[cocompact ℂ] fun z => z⁻¹ ^ 2 * H z⁻¹) : ∀ z, F z = 0 :=
  entire_eq_zero_of_inverse_germ (m := 2) hF hH (by decide) hinfty

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsSphere
