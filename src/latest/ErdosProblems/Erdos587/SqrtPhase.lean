import ErdosProblems.Erdos587.CriticalScale
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Exact derivatives of the affine square-root phase used in the fiber argument. -/

open scoped Topology ContDiff

namespace Erdos587

noncomputable def sqrtAffinePhase (a b x : ℝ) : ℝ := Real.sqrt (a + b * x)
noncomputable def sqrtAffinePhaseD1 (a b x : ℝ) : ℝ :=
  b / 2 * (a + b * x) ^ (-(1 / 2 : ℝ))
noncomputable def sqrtAffinePhaseD2 (a b x : ℝ) : ℝ :=
  -(b ^ 2) / 4 * (a + b * x) ^ (-(3 / 2 : ℝ))
noncomputable def sqrtAffinePhaseD3 (a b x : ℝ) : ℝ :=
  3 * b ^ 3 / 8 * (a + b * x) ^ (-(5 / 2 : ℝ))

lemma hasDerivAt_affine_rpow (a b p x : ℝ) (hx : 0 < a + b * x) :
    HasDerivAt (fun y : ℝ => (a + b * y) ^ p) (b * p * (a + b * x) ^ (p - 1)) x := by
  have hh : HasDerivAt (fun y : ℝ => a + b * y) b x := by
    exact (hasDerivAt_const_mul b).const_add a
  exact hh.rpow_const (Or.inl hx.ne')

lemma hasDerivAt_sqrtAffinePhase (a b x : ℝ) (hx : 0 < a + b * x) :
    HasDerivAt (sqrtAffinePhase a b) (sqrtAffinePhaseD1 a b x) x := by
  have hh := hasDerivAt_affine_rpow a b (1 / 2) x hx
  norm_num at hh
  change HasDerivAt (fun y : ℝ => Real.sqrt (a + b * y))
    (b / 2 * (a + b * x) ^ (-(1 / 2 : ℝ))) x
  simpa only [Real.sqrt_eq_rpow, div_eq_mul_inv, one_mul] using hh

lemma hasDerivAt_sqrtAffinePhaseD1 (a b x : ℝ) (hx : 0 < a + b * x) :
    HasDerivAt (sqrtAffinePhaseD1 a b) (sqrtAffinePhaseD2 a b x) x := by
  have hh := (hasDerivAt_affine_rpow a b (-(1 / 2)) x hx).const_mul (b / 2)
  norm_num at hh
  have heq : -(b / 2 * (b * (1 / 2) * (a + b * x) ^ (-(3 / 2 : ℝ)))) =
      -(b ^ 2) / 4 * (a + b * x) ^ (-(3 / 2 : ℝ)) := by ring
  rw [heq] at hh
  exact hh

lemma hasDerivAt_sqrtAffinePhaseD2 (a b x : ℝ) (hx : 0 < a + b * x) :
    HasDerivAt (sqrtAffinePhaseD2 a b) (sqrtAffinePhaseD3 a b x) x := by
  have hh := (hasDerivAt_affine_rpow a b (-(3 / 2)) x hx).const_mul (-(b ^ 2) / 4)
  norm_num at hh
  have heq : -(-(b ^ 2) / 4 * (b * (3 / 2) * (a + b * x) ^ (-(5 / 2 : ℝ)))) =
      3 * b ^ 3 / 8 * (a + b * x) ^ (-(5 / 2 : ℝ)) := by ring
  rw [heq] at hh
  exact hh

lemma sqrtAffinePhaseD2_neg {a b x : ℝ} (hb : 0 < b) (hx : 0 < a + b * x) :
    sqrtAffinePhaseD2 a b x < 0 := by
  unfold sqrtAffinePhaseD2
  exact mul_neg_of_neg_of_pos
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos hb)) (by norm_num))
    (Real.rpow_pos_of_pos hx _)

lemma sqrtAffinePhaseD3_pos {a b x : ℝ} (hb : 0 < b) (hx : 0 < a + b * x) :
    0 < sqrtAffinePhaseD3 a b x := by
  unfold sqrtAffinePhaseD3
  positivity

lemma contDiffOn_sqrtAffinePhase (a b : ℝ) :
    ContDiffOn ℝ ∞ (sqrtAffinePhase a b) {x : ℝ | 0 < a + b * x} := by
  have hh : ContDiffOn ℝ ∞ (fun x : ℝ => a + b * x) {x : ℝ | 0 < a + b * x} := by
    fun_prop
  change ContDiffOn ℝ ∞ (fun x : ℝ => Real.sqrt (a + b * x)) {x : ℝ | 0 < a + b * x}
  simpa only [Real.sqrt_eq_rpow] using
    hh.rpow_const_of_ne (p := (1 / 2 : ℝ)) (fun x hx => ne_of_gt hx)

end Erdos587
