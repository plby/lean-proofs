import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Dividing an analytic function that vanishes at the origin

The exterior term in the normalized additive Cousin splitting vanishes at
infinity.  Dividing its expression in the coordinate `u = 1/z` by `u`
therefore gives the transition formula for `O(-1)`.
-/

noncomputable section

open Complex Metric Set

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The divided difference is holomorphic on the same disc as the original
function, including at the removable point zero. -/
theorem analyticOnNhd_dslope_zero {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) :
    AnalyticOnNhd ℂ (dslope f 0) (ball 0 R) :=
  (analyticOnNhd_iff_differentiableOn isOpen_ball).mpr
    ((differentiableOn_dslope (ball_mem_nhds (0 : ℂ) hR)).mpr hf.differentiableOn)

/-- This is an exact factorization, not just an equality of germs. -/
theorem zero_mul_dslope {f : ℂ → ℂ} (hf : f 0 = 0) (z : ℂ) :
    z * dslope f 0 z = f z := by
  simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope_of_zero hf z

/-- An analytic function vanishing at the origin has an analytic quotient
by the coordinate on its entire disc of definition. -/
theorem exists_analytic_factor_at_zero {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (hf₀ : f 0 = 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R) ∧
      (∀ z, z * g z = f z) ∧ g 0 = deriv f 0 :=
  ⟨dslope f 0, analyticOnNhd_dslope_zero hR hf, zero_mul_dslope hf₀, dslope_same f 0⟩

end Wikipedia.HopfProblem.HolomorphicCousin
