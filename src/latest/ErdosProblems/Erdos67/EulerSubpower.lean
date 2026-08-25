import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The subpower error in the Euler--residue argument

The Euler-product comparison in the proof of Erdos problem 67 produces an
error of size `exp (C * sqrt (log log X))`, where `C` is fixed before `X`
tends to infinity.  This file records the precise asymptotic fact needed by
the residue-class argument: that error is little-oh of `log X`.
-/

open Filter Asymptotics
open scoped Topology

namespace Erdos67.EulerSubpower

noncomputable section

/-- The subpower error occurring in the twisted Euler-product comparison. -/
def subpowerError (C : ℝ) (X : ℕ) : ℝ :=
  Real.exp (C * Real.sqrt (Real.log (Real.log (X : ℝ))))

theorem tendsto_log_nat_atTop :
    Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_log_log_nat_atTop :
    Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_nat_atTop

/-- A fixed multiple of `sqrt x` is eventually at most `x / 2`. -/
theorem eventually_mul_sqrt_le_half (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * Real.sqrt x ≤ x / 2 := by
  have hsqrt : Tendsto (fun x : ℝ ↦ Real.sqrt x) atTop atTop :=
    Real.tendsto_sqrt_atTop
  filter_upwards [hsqrt.eventually (eventually_ge_atTop (2 * max C 0)),
      eventually_ge_atTop 0] with x hx hx0
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hC : C ≤ Real.sqrt x / 2 := by
    have : 2 * max C 0 ≤ Real.sqrt x := hx
    linarith [le_max_left C 0]
  have hsquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
  nlinarith

theorem tendsto_id_sub_mul_sqrt_atTop (C : ℝ) :
    Tendsto (fun x : ℝ ↦ x - C * Real.sqrt x) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_mul_sqrt_le_half C] with x hx
  dsimp
  linarith

/-- On the real line, `exp (C sqrt(log y)) = o(y)`. -/
theorem subpower_real_isLittleO (C : ℝ) :
    (fun y : ℝ ↦ Real.exp (C * Real.sqrt (Real.log y))) =o[atTop]
      (fun y : ℝ ↦ y) := by
  have hExp :
      (fun y : ℝ ↦ Real.exp (C * Real.sqrt (Real.log y))) =o[atTop]
        (fun y : ℝ ↦ Real.exp (Real.log y)) := by
    rw [Real.isLittleO_exp_comp_exp_comp]
    simpa only [Pi.sub_apply, Function.comp_def] using
      (tendsto_id_sub_mul_sqrt_atTop C).comp Real.tendsto_log_atTop
  refine hExp.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  exact Real.exp_log hy

/-- The error `exp (C sqrt(log log X))` is little-oh of `log X`. -/
theorem subpowerError_isLittleO_log (C : ℝ) :
    (subpowerError C) =o[atTop] (fun X : ℕ ↦ Real.log (X : ℝ)) := by
  change (fun X : ℕ ↦
      Real.exp (C * Real.sqrt (Real.log (Real.log (X : ℝ))))) =o[atTop]
        (fun X : ℕ ↦ Real.log (X : ℝ))
  simpa only [Function.comp_apply, Function.comp_def] using
    (subpower_real_isLittleO C).comp_tendsto tendsto_log_nat_atTop

/-- Epsilon form used to absorb the Euler-product error into the main term. -/
theorem eventually_subpowerError_le_mul_log (C : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℕ in atTop,
      subpowerError C X ≤ epsilon * Real.log (X : ℝ) := by
  have hbound := (subpowerError_isLittleO_log C).bound hepsilon
  filter_upwards [hbound,
      tendsto_log_nat_atTop.eventually (eventually_ge_atTop 0)] with X hX hlog
  simpa only [subpowerError, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.norm_of_nonneg hlog] using hX

end

end Erdos67.EulerSubpower
