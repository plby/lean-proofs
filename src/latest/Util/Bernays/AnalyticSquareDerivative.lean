import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Derivative bounds for a holomorphic square root

These estimates do not choose a branch of the square root. They apply directly
to an analytic function whose square has bounded derivative on a larger region.
-/

open Set Metric

namespace Bernays

theorem deriv_square_norm {f F : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (_hF : DifferentiableAt ℂ F z)
    (heq : F =ᶠ[nhds z] fun w => f w ^ 2) :
    ‖deriv F z‖ = 2 * ‖f z‖ * ‖deriv f z‖ := by
  have hd := (hf.hasDerivAt.pow 2).congr_of_eventuallyEq heq
  rw [hd.deriv]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, norm_mul, Complex.norm_ofNat]

theorem norm_le_sqrt_of_sq_eq {u v : ℂ} {a : ℝ} (heq : u ^ 2 = v) (hv : ‖v‖ ≤ a) :
    ‖u‖ ≤ Real.sqrt a := by
  apply (Real.le_sqrt (norm_nonneg _) ((norm_nonneg v).trans hv)).mpr
  rw [← norm_pow, heq]
  exact hv

theorem sqrt_mul_norm_deriv_le {f F : ℂ → ℂ} {z : ℂ} {r L : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L)
    (hf : DiffContOnCl ℂ f (ball z r))
    (hF : DifferentiableAt ℂ F z)
    (heq : ∀ w ∈ closedBall z r, F w = f w ^ 2)
    (hderiv : ‖deriv F z‖ ≤ L)
    (hvar : ∀ w ∈ sphere z r, ‖F w - F z‖ ≤ L * r) :
    Real.sqrt r * ‖deriv f z‖ ≤ L + 1 := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsrsq := Real.sq_sqrt hr.le
  have hcenter := heq z (mem_closedBall_self hr.le)
  by_cases hsmall : ‖f z‖ ^ 2 ≤ r
  · have hbound : ∀ w ∈ sphere z r, ‖f w‖ ≤ Real.sqrt ((L + 1) * r) := by
      intro w hw
      apply norm_le_sqrt_of_sq_eq (heq w (sphere_subset_closedBall hw)).symm
      have hval : ‖F z‖ ≤ r := by simpa only [hcenter, norm_pow] using hsmall
      calc
        ‖F w‖ = ‖(F w - F z) + F z‖ := by rw [sub_add_cancel]
        _ ≤ ‖F w - F z‖ + ‖F z‖ := norm_add_le _ _
        _ ≤ L * r + r := add_le_add (hvar w hw) hval
        _ = (L + 1) * r := by ring
    have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hf hbound
    have hsqrt : Real.sqrt ((L + 1) * r) = Real.sqrt (L + 1) * Real.sqrt r :=
      Real.sqrt_mul (by linarith) _
    rw [hsqrt] at hC
    have hprod := (le_div_iff₀ hr).mp hC
    have hstep : Real.sqrt r * ‖deriv f z‖ ≤ Real.sqrt (L + 1) := by
      have hid : ‖deriv f z‖ * r = Real.sqrt r * (Real.sqrt r * ‖deriv f z‖) := by
        calc
          _ = ‖deriv f z‖ * Real.sqrt r ^ 2 := congrArg (‖deriv f z‖ * ·) hsrsq.symm
          _ = _ := by ring
      rw [hid, mul_comm (Real.sqrt (L + 1)) (Real.sqrt r)] at hprod
      exact (mul_le_mul_iff_right₀ hsr).mp hprod
    apply hstep.trans
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  · have hbig : Real.sqrt r ≤ ‖f z‖ := by nlinarith [norm_nonneg (f z)]
    have hevent : F =ᶠ[nhds z] fun w => f w ^ 2 :=
      Filter.eventually_of_mem (closedBall_mem_nhds z hr) heq
    have hnorm := deriv_square_norm (hf.differentiableAt isOpen_ball (mem_ball_self hr)) hF hevent
    have hnonneg := norm_nonneg (deriv f z)
    nlinarith [mul_le_mul_of_nonneg_right hbig hnonneg]

theorem sqrt_mul_norm_deriv_le_of_deriv_bound {f F : ℂ → ℂ} {z : ℂ} {r L : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L)
    (hf : DiffContOnCl ℂ f (ball z r))
    (hF : ∀ w ∈ closedBall z r, DifferentiableAt ℂ F w)
    (heq : ∀ w ∈ closedBall z r, F w = f w ^ 2)
    (hderiv : ∀ w ∈ closedBall z r, ‖deriv F w‖ ≤ L) :
    Real.sqrt r * ‖deriv f z‖ ≤ L + 1 := by
  apply sqrt_mul_norm_deriv_le hr hL hf (hF z (mem_closedBall_self hr.le)) heq
    (hderiv z (mem_closedBall_self hr.le))
  intro w hw
  have h := (convex_closedBall z r).norm_image_sub_le_of_norm_deriv_le hF hderiv
    (mem_closedBall_self hr.le) (sphere_subset_closedBall hw)
  simpa only [mem_sphere_iff_norm.mp hw] using h

end Bernays
