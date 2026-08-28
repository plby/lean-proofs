import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The descending linear field in quadratic Morse coordinates

The field `(u, -v)` increases the negative coordinate and decreases the
positive one. The actual derivative of `-‖u‖² + ‖v‖²` is strictly negative
away from the origin, in all index cases including zero-dimensional factors.
-/

noncomputable section

open scoped ContDiff RealInnerProductSpace

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

variable {N P : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]

def quadratic (z : N × P) : ℝ := -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2

def descent (z : N × P) : N × P := (z.1, -z.2)

theorem contDiff_descent : ContDiff ℝ ∞ (descent (N := N) (P := P)) :=
  contDiff_fst.prodMk contDiff_snd.neg

theorem contDiff_quadratic : ContDiff ℝ ∞ (quadratic (N := N) (P := P)) :=
  (contDiff_fst.norm_sq ℝ).neg.add (contDiff_snd.norm_sq ℝ)

/-- The actual derivative of the quadratic Morse function along its descending field. -/
theorem fderiv_quadratic_descent (z : N × P) :
    fderiv ℝ quadratic z (descent z) = -2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) := by
  have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).norm_sq.neg.add
    (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).norm_sq
  have hd' := hd.fderiv
  change fderiv ℝ quadratic z = _ at hd'
  rw [hd']
  simp only [descent, add_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', innerSL_apply_apply,
    inner_neg_right, real_inner_self_eq_norm_sq, two_smul]
  ring

theorem fderiv_quadratic_descent_nonpos (z : N × P) :
    fderiv ℝ quadratic z (descent z) ≤ 0 := by
  rw [fderiv_quadratic_descent]
  nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]

theorem fderiv_quadratic_descent_neg {z : N × P} (hz : z ≠ 0) :
    fderiv ℝ quadratic z (descent z) < 0 := by
  rw [fderiv_quadratic_descent]
  have hsum : 0 < ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
    by_contra! h
    have hu : ‖z.1‖ = 0 := by nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
    have hv : ‖z.2‖ = 0 := by nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
    exact hz (Prod.ext (norm_eq_zero.mp hu) (norm_eq_zero.mp hv))
  nlinarith

end Wikipedia.SmoothSixDPoincare.MorseHandle
