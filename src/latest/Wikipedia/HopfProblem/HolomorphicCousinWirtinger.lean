import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.LinearCombination

/-!
# The antiholomorphic derivative on the complex plane

This file fixes the normalization of `∂̄` used by the Cauchy--Green solver.
Its vanishing is equivalent to the Cauchy--Riemann equation for a
real-differentiable function, so correcting a smooth local cochain by a
solution of its `∂̄` equation gives holomorphic local sections.
-/

noncomputable section

open Complex Set
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The antiholomorphic component of a continuous real-linear differential. -/
def dbarLinear : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / (2 : ℂ)) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) +
    I • ContinuousLinearMap.apply ℝ ℂ I)

@[simp] theorem dbarLinear_apply (L : ℂ →L[ℝ] ℂ) :
    dbarLinear L = (L 1 + I * L I) / 2 := by
  simp only [dbarLinear, smul_apply, add_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

/-- The antiholomorphic derivative `∂̄f = (∂ₓf + i∂ᵧf)/2`. -/
def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2

theorem dbar_eq_dbarLinear (f : ℂ → ℂ) (z : ℂ) :
    dbar f z = dbarLinear (fderiv ℝ f z) := (dbarLinear_apply _).symm

theorem dbarLinear_complex_smul (c : ℂ) (L : ℂ →L[ℝ] ℂ) :
    dbarLinear (c • L) = c * dbarLinear L := by
  simp only [dbarLinear_apply, smul_apply, smul_eq_mul]
  ring

/-- The vanishing condition is exactly the real-linear Cauchy--Riemann equation. -/
theorem dbar_eq_zero_iff (f : ℂ → ℂ) (z : ℂ) :
    dbar f z = 0 ↔ fderiv ℝ f z I = I * fderiv ℝ f z 1 := by
  constructor
  · intro h
    have hs : fderiv ℝ f z 1 + I * fderiv ℝ f z I = 0 := by
      simpa only [dbar, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using h
    have hm := congrArg (fun w : ℂ => -I * w) hs
    simp only [mul_add, neg_mul, ← mul_assoc, I_mul_I, neg_neg, mul_zero] at hm
    linear_combination hm
  · intro h
    rw [dbar, h, ← mul_assoc, I_mul_I, neg_one_mul, add_neg_cancel, zero_div]

/-- Real differentiability together with `∂̄f = 0` gives genuine complex
differentiability, rather than an assumed analytic structure. -/
theorem differentiableAt_complex_iff_dbar {f : ℂ → ℂ} {z : ℂ} :
    DifferentiableAt ℂ f z ↔ DifferentiableAt ℝ f z ∧ dbar f z = 0 := by
  rw [differentiableAt_complex_iff_differentiableAt_real, dbar_eq_zero_iff]
  rfl

theorem dbar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : dbar f z = 0 :=
  (differentiableAt_complex_iff_dbar.mp hf).2

/-- On an open set the smooth Cauchy--Riemann equation implies analyticity. -/
theorem analyticOnNhd_of_dbar_eq_zero {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (hd : ∀ z ∈ U, dbar f z = 0) : AnalyticOnNhd ℂ f U := by
  apply (analyticOnNhd_iff_differentiableOn hU).mpr
  intro z hz
  exact ((differentiableAt_complex_iff_dbar).mpr
    ⟨(hf z hz).differentiableAt (hU.mem_nhds hz), hd z hz⟩).differentiableWithinAt

@[simp] theorem dbar_const (c z : ℂ) : dbar (fun _ => c) z = 0 := by
  simp [dbar]

theorem dbar_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w + g w) z = dbar f z + dbar g z := by
  simp only [dbar_eq_dbarLinear, fderiv_fun_add hf hg, map_add]

theorem dbar_sub {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w - g w) z = dbar f z - dbar g z := by
  simp only [dbar_eq_dbarLinear, fderiv_fun_sub hf hg, map_sub]

theorem dbar_const_mul {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (c : ℂ) :
    dbar (fun w => c * f w) z = c * dbar f z := by
  simp only [dbar_eq_dbarLinear, fderiv_const_mul hf c, dbarLinear_complex_smul]

theorem dbar_mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w * g w) z = f z * dbar g z + g z * dbar f z := by
  simp only [dbar_eq_dbarLinear, fderiv_fun_mul hf hg, map_add, dbarLinear_complex_smul]

/-- Translation of the argument commutes with `∂̄`. -/
theorem dbar_comp_sub (f : ℂ → ℂ) (a z : ℂ) :
    dbar (fun w => f (w - a)) z = dbar f (z - a) := by
  simp only [dbar, fderiv_comp_sub]

/-- Reflection about a fixed point changes the sign of `∂̄`. -/
theorem dbar_comp_const_sub {f : ℂ → ℂ} (a z : ℂ)
    (hf : DifferentiableAt ℝ f (a - z)) :
    dbar (fun w => f (a - w)) z = -dbar f (a - z) := by
  have hi : HasFDerivAt (fun w : ℂ => a - w) (-ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).const_sub a
  have he := (hf.hasFDerivAt.comp z hi).fderiv
  change fderiv ℝ (fun w => f (a - w)) z = _ at he
  simp only [dbar, he, ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]
  ring

/-- Taking an antiholomorphic derivative does not enlarge the closed support. -/
theorem tsupport_dbar_subset (f : ℂ → ℂ) : tsupport (dbar f) ⊆ tsupport f := by
  have he : dbar f = dbarLinear ∘ fderiv ℝ f := funext (dbar_eq_dbarLinear f)
  rw [he]
  exact (tsupport_comp_subset (map_zero dbarLinear) _).trans (tsupport_fderiv_subset ℝ)

theorem hasCompactSupport_dbar {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (dbar f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_dbar_subset f)

theorem continuous_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (dbar f) := by
  have he : dbar f = dbarLinear ∘ fderiv ℝ f := funext (dbar_eq_dbarLinear f)
  rw [he]
  exact dbarLinear.continuous.comp (hf.continuous_fderiv one_ne_zero)

theorem contDiff_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (dbar f) := by
  have he : dbar f = dbarLinear ∘ fderiv ℝ f := funext (dbar_eq_dbarLinear f)
  rw [he]
  exact dbarLinear.contDiff.comp (contDiff_infty_iff_fderiv.mp hf).2

theorem contDiffAt_dbar {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (dbar f) z := by
  have he : dbar f = dbarLinear ∘ fderiv ℝ f := funext (dbar_eq_dbarLinear f)
  rw [he]
  exact dbarLinear.contDiff.contDiffAt.comp z (hf.fderiv_right (by simp))

theorem contDiffOn_dbar {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (dbar f) U := by
  intro z hz
  exact (contDiffAt_dbar ((hf z hz).contDiffAt (hU.mem_nhds hz))).contDiffWithinAt

/-- Two smooth local representatives of an additive cocycle have the same
antiholomorphic derivative whenever their difference is holomorphic. -/
theorem dbar_eq_of_sub_differentiableAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hfg : DifferentiableAt ℂ (fun w => f w - g w) z) : dbar f z = dbar g z := by
  have he := dbar_eq_zero_of_differentiableAt hfg
  rw [dbar_sub hf hg] at he
  exact sub_eq_zero.mp he

end Wikipedia.HopfProblem.HolomorphicCousin
