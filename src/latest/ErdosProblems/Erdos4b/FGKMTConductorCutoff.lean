/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSqrtLogGrowth
import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanPowers
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# A natural conductor cutoff in the exponential window

Floors are retained explicitly. All eventual bounds use a fixed positive
exponent before the endpoint tends to infinity.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter BoundedGaps.Maynard

def effectiveConductorCutoff (a : ℝ) (x : ℕ) : ℕ :=
  ⌊Real.exp (a * Real.sqrt (Real.log (x : ℝ)))⌋₊

theorem effectiveConductorCutoff_le_exp (a : ℝ) (x : ℕ) :
    (effectiveConductorCutoff a x : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) :=
  Nat.floor_le (Real.exp_pos _).le

theorem eventually_effectiveConductorCutoff_window {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop,
      2 ≤ effectiveConductorCutoff a x ∧
      Real.exp ((a / 2) * Real.sqrt (Real.log (x : ℝ))) ≤ effectiveConductorCutoff a x ∧
      (effectiveConductorCutoff a x : ℝ) ≤ vaughanCubeRoot x := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have huTop := Real.tendsto_sqrt_atTop.comp hlogTop
  have hvTop := Real.tendsto_exp_atTop.comp
    (huTop.const_mul_atTop (by positivity : 0 < a / 2))
  filter_upwards [hvTop.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_exp_mul_sqrtLog_le_rpow a (by norm_num : (0 : ℝ) < 1 / 3)] with x hv hpow
  let v := Real.exp ((a / 2) * Real.sqrt (Real.log (x : ℝ)))
  have hv2 : 2 ≤ v := by simpa only [Function.comp_apply] using hv
  have hsq : Real.exp (a * Real.sqrt (Real.log (x : ℝ))) = v ^ 2 := by
    dsimp [v]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hfloor : v ^ 2 / 2 < (effectiveConductorCutoff a x : ℝ) := by
    simpa only [effectiveConductorCutoff, hsq] using
      (Nat.div_two_lt_floor (by rw [hsq]; nlinarith :
        (1 : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ)))))
  have hvfloor : v ≤ (effectiveConductorCutoff a x : ℝ) :=
    (by nlinarith : v ≤ v ^ 2 / 2).trans hfloor.le
  refine ⟨?_, hvfloor, ?_⟩
  · exact_mod_cast hv2.trans hvfloor
  · exact (effectiveConductorCutoff_le_exp a x).trans hpow

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_effectiveConductorCutoff_window
