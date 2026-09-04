module
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import ErdosProblems.Erdos515.External.Ray.Misc.Bound
import ErdosProblems.Erdos515.External.Ray.Misc.Bounds

/-!
## Facts about `Complex.pow`
-/

open Set

variable {z w : ℂ}

/-- `Complex.pow` and `pow` interact nicely -/
public lemma pow_mul_nat {z w : ℂ} {n : ℕ} : (z ^ w) ^ n = z ^ (w * n) := by
  by_cases z0 : z = 0
  · rw [z0]
    by_cases w0 : w = 0; · rw [w0]; simp
    by_cases n0 : n = 0; · rw [n0]; simp
    have wn0 : w * n ≠ 0 := mul_ne_zero w0 (Nat.cast_ne_zero.mpr n0)
    rw [Complex.zero_cpow w0]
    rw [Complex.zero_cpow wn0]
    exact zero_pow n0
  simp only [Complex.cpow_def_of_ne_zero z0, ← Complex.exp_nat_mul]
  ring_nf

/-- Bound `cpow` in terms of `rpow` -/
public lemma Complex.norm_one_sub_cpow_sub_one_le_rpow_sub_one {a : ℝ} (z1 : ‖z‖ < 1) (a0 : a ≤ 0) :
    ‖(1 - z) ^ (a : ℂ) - 1‖ ≤ (1 - ‖z‖) ^ a - 1 := by
  by_cases z0 : z = 0
  · simp [z0]
  generalize hx : ‖z‖ = x
  generalize hw : z / ‖z‖ = w
  have zx : z = x * w := by rw [← hx, ← hw]; field_simp [z0]
  have x0 : 0 ≤ x := by simp only [← hx, norm_nonneg]
  have w1 : ‖w‖ = 1 := by simp [← hw, z0]
  simp only [zx]
  have i : ∀ w : ℂ, ‖w‖ = 1 → (1 - x * w) ^ (a : ℂ) - 1 =
      ∫ t in 0..x, a * (1 - t * w) ^ (a - 1 : ℂ) * -w := by
    intro w w1
    have o : 1 = (1 - (0 : ℝ) * w) ^ (a : ℂ) := by simp
    nth_rw 2 [o]
    have df : ∀ t ∈ uIcc 0 x, HasDerivAt (fun t : ℝ ↦ (1 - t * w) ^ (a : ℂ))
        (a * (1 - t * w) ^ (a - 1 : ℂ) * -w) t := by
      intro t ⟨t0, tx⟩
      simp only [x0, inf_of_le_left, sup_of_le_right] at t0 tx
      refine (HasDerivAt.cpow_const (f := fun t ↦ 1 - t * w) (c := a) (x := t)
        (f' := -w) ((hasDerivAt_mul_const _).const_sub _) ?_).comp_ofReal
      exact mem_slitPlane_of_near_one (by simp [w1, abs_of_nonneg t0]; linarith)
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (E := ℂ) df ?_).symm
    apply ContinuousOn.intervalIntegrable_of_Icc x0
    refine ContinuousOn.mul (continuousOn_const.mul (ContinuousOn.cpow_const (by fun_prop)
      fun t ⟨t0,tx⟩ ↦ ?_)) continuousOn_const
    exact mem_slitPlane_of_near_one (by simp [w1, abs_of_nonneg t0]; linarith)
  trans ‖(1 - x * (1 : ℂ)) ^ (a : ℂ) - 1‖
  · rw [i w w1, i 1 (by simp)]
    simp only [mul_neg, intervalIntegral.integral_neg, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul, norm_neg, Complex.norm_mul, norm_real, Real.norm_eq_abs,
      w1, mul_one]
    have e : EqOn (fun t : ℝ ↦ (1 - (t : ℂ)) ^ (a - 1 : ℂ)) (fun t ↦ (((1 - t) ^ (a - 1) : ℝ) : ℂ))
        (uIcc 0 x) := by
      intro t ⟨t0, tx⟩
      simp only [x0, inf_of_le_left, sup_of_le_right] at t0 tx ⊢
      rw [Complex.ofReal_cpow (by linarith)]
      simp
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_ofReal, Complex.norm_real]
    refine mul_le_mul_of_nonneg_left ?_ (by bound)
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · refine intervalIntegral.norm_integral_le_of_norm_le x0 (.of_forall ?_) ?_
      · intro t ⟨t0,tx⟩
        simp only [(by simp : (a : ℂ) - 1 = (a - 1 : ℝ)), Complex.norm_cpow_real]
        refine Real.rpow_le_rpow_of_nonpos (by linarith) ?_ (by linarith)
        calc ‖1 - t * w‖
          _ ≥ ‖(1 : ℂ)‖ - ‖t * w‖ := by bound
          _ = 1 - t := by simp [abs_of_pos t0, w1]
      · apply ContinuousOn.intervalIntegrable_of_Icc x0
        apply ContinuousOn.rpow_const (by fun_prop)
        intro t ⟨t0,tx⟩
        left
        linarith
    · exact intervalIntegral.integral_nonneg x0 fun t ⟨t0,tx⟩ ↦ by bound
  · simp only [mul_one, (by simp : (1 - x : ℂ) = (1 - x : ℝ))]
    nth_rw 1 [← Complex.ofReal_one]
    rw [← Complex.ofReal_cpow (by linarith), ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg]
    bound

/-- Bound `cpow` in terms of `rpow` -/
public lemma Complex.norm_one_add_cpow_sub_one_le_rpow_sub_one {a : ℝ} (z1 : ‖z‖ < 1) (a0 : a ≤ 0) :
    ‖(1 + z) ^ (a : ℂ) - 1‖ ≤ (1 - ‖z‖) ^ a - 1 := by
  simpa using Complex.norm_one_sub_cpow_sub_one_le_rpow_sub_one (z := -z) (by simpa) a0

/-- Convexity of `rpow` for nonpositive powers -/
lemma Real.convexOn_rpow_of_neg {p : ℝ} (p0 : p ≤ 0) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ ↦ x ^ p) := by
  set f := fun x : ℝ ↦ x ^ p
  set f' := fun x : ℝ ↦ p * x ^ (p - 1)
  set f'' := fun x : ℝ ↦ p * ((p - 1) * x ^ (p - 1 - 1))
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'')
  · intro x x0
    simp only [mem_Ioi] at x0
    apply ((Real.continuousAt_rpow_of_ne _ (by simp [x0.ne'])).comp₂ ?_ ?_).continuousWithinAt
    all_goals fun_prop
  · intro x x0
    simp only [interior_Ioi, mem_Ioi] at x0
    exact (Real.hasStrictDerivAt_rpow_const_of_ne x0.ne' _).hasDerivAt.hasDerivWithinAt
  · intro x x0
    simp only [interior_Ioi, mem_Ioi] at x0
    exact ((Real.hasStrictDerivAt_rpow_const_of_ne x0.ne' _).hasDerivAt.const_mul _
      ).hasDerivWithinAt
  · intro x x0
    simp only [interior_Ioi, mem_Ioi, ← mul_assoc, f''] at x0 ⊢
    exact mul_nonneg (by nlinarith) (by bound)
  · apply convex_Ioi

/-- Bound `(1 - x) ^ -a - 1` linearly, optimally -/
public lemma Real.one_sub_rpow_neg_sub_one_le_linear {x y a : ℝ} (x0 : 0 ≤ x) (xy : x ≤ y)
    (y1 : y < 1) (a0 : a ≤ 0) : (1 - x) ^ a - 1 ≤ ((1 - y) ^ a - 1) / y * x := by
  by_cases xz : x = 0
  · simp [xz]
  · replace x0 : 0 < x := (Ne.symm xz).lt_of_le x0
    rw [← div_le_iff₀ (by linarith)]
    simpa [slope, ← div_eq_inv_mul] using (Real.convexOn_rpow_of_neg a0).slope_mono (x := 1)
      (by simp) (a := 1 - y) (b := 1 - x) (by simp only [mem_sdiff, mem_Ioi, sub_pos, mem_singleton_iff, sub_eq_self]; bound) (by simp only [mem_sdiff, mem_Ioi, sub_pos, mem_singleton_iff, sub_eq_self]; bound) (by bound)
