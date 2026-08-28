import Wikipedia.HopfProblem.HolomorphicCousinConvolutionDbar
import Wikipedia.HopfProblem.HolomorphicCousinGreenIdentity

/-!
# The actual compact-support solution of the antiholomorphic derivative equation

The fundamental Cauchy–Green identity, applied after reflection about the
evaluation point, proves that the convergent Cauchy–Green convolution solves
`∂̄u = f`. The solver is smooth when the compactly supported data are smooth.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The Cauchy–Green operator recovers a compactly supported function from its
antiholomorphic derivative. -/
theorem cauchyGreen_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) :
    cauchyGreen (dbar f) z = f z := by
  let φ : ℂ → ℂ := fun w => f (z - w)
  have hφ : ContDiff ℝ 1 φ := hf.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hcf.comp_homeomorph (Homeomorph.subLeft z)
  have hd : dbar φ = fun w => -dbar f (z - w) := by
    funext w
    exact dbar_comp_const_sub z w ((hf.differentiable one_ne_zero) (z - w))
  have he := integral_inv_mul_dbar hφ hcφ
  have he' : -(∫ w : ℂ, w⁻¹ * dbar f (z - w)) =
      -((Real.pi : ℂ) * f z) := by
    simpa only [hd, mul_neg, integral_neg, φ, sub_zero, neg_mul] using he
  have hi := neg_injective he'
  unfold cauchyGreen
  rw [hi, one_div, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

/-- **The compact-support Cauchy–Green solution:** its antiholomorphic
derivative is the prescribed data. -/
theorem dbar_cauchyGreen {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) :
    dbar (cauchyGreen f) z = f z := by
  rw [dbar_cauchyGreen_eq_cauchyGreen_dbar hf hcf, cauchyGreen_dbar hf hcf]

/-- Smooth compactly supported data have a concrete smooth solution. -/
theorem cauchyGreen_smooth_dbar_solution {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) :
    ContDiff ℝ ∞ (cauchyGreen f) ∧ ∀ z, dbar (cauchyGreen f) z = f z := by
  refine ⟨contDiff_cauchyGreen hf hcf, ?_⟩
  exact dbar_cauchyGreen (hf.of_le (by simp)) hcf

/-- Existence is witnessed by the actual convergent convolution. -/
theorem exists_smooth_dbar_solution {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) :
    ∃ u : ℂ → ℂ, ContDiff ℝ ∞ u ∧ ∀ z, dbar u z = f z :=
  ⟨cauchyGreen f, cauchyGreen_smooth_dbar_solution hf hcf⟩

/-- Away from the closed support of the data, the solution is genuinely holomorphic. -/
theorem analyticOnNhd_cauchyGreen_compl_tsupport {f : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) :
    AnalyticOnNhd ℂ (cauchyGreen f) (tsupport f)ᶜ := by
  apply analyticOnNhd_of_dbar_eq_zero (isClosed_tsupport f).isOpen_compl
  · intro z _
    exact (hasFDerivAt_cauchyGreen hf hcf z).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [dbar_cauchyGreen hf hcf]
    exact image_eq_zero_of_notMem_tsupport hz

end Wikipedia.HopfProblem.HolomorphicCousin
