/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.Base
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Elementary monotonicity for the exact Rankin expression

The factor v log(log v)/(log v)^2 is nondecreasing for v ≥ exp 2.
This follows from the proved antitonicity of log v / sqrt v.
-/

namespace Erdos4b

noncomputable section

def rankinFactor (v : ℝ) : ℝ := v * Real.log (Real.log v) / Real.log v ^ 2

theorem self_div_log_sq_monotoneOn :
    MonotoneOn (fun v : ℝ ↦ v / Real.log v ^ 2) (Set.Ici (Real.exp 2)) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := (Real.exp_pos 2).trans_le hx
  have hypos : 0 < y := hxpos.trans_le hxy
  have hlogx : 0 < Real.log x := by
    have hh : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
    linarith
  have hlogy : 0 < Real.log y := hlogx.trans_le (Real.log_le_log hxpos hxy)
  have hh := Real.log_div_sqrt_antitoneOn hx hy hxy
  have hs : (Real.log y / Real.sqrt y) ^ 2 ≤ (Real.log x / Real.sqrt x) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hlogy.le (Real.sqrt_nonneg y)) hh 2
  rw [div_pow, div_pow, Real.sq_sqrt hypos.le, Real.sq_sqrt hxpos.le] at hs
  have hinv := one_div_le_one_div_of_le (div_pos (sq_pos_of_pos hlogy) hypos) hs
  simpa only [one_div, inv_div] using hinv

theorem rankinFactor_nonneg {v : ℝ} (hv : Real.exp 2 ≤ v) : 0 ≤ rankinFactor v := by
  have hvpos : 0 < v := (Real.exp_pos 2).trans_le hv
  have hlog : 2 ≤ Real.log v := (Real.le_log_iff_exp_le hvpos).mpr hv
  exact div_nonneg (mul_nonneg hvpos.le (Real.log_nonneg (by linarith))) (sq_nonneg _)

theorem rankinFactor_monotoneOn : MonotoneOn rankinFactor (Set.Ici (Real.exp 2)) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := (Real.exp_pos 2).trans_le hx
  have hypos : 0 < y := hxpos.trans_le hxy
  have hlogx : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hx
  have hlogxy := Real.log_le_log hxpos hxy
  have hlogs := Real.log_le_log (show 0 < Real.log x by linarith) hlogxy
  have hratio := self_div_log_sq_monotoneOn hx hy hxy
  have hh := mul_le_mul hratio hlogs (Real.log_nonneg (show 1 ≤ Real.log x by linarith))
    (div_nonneg hypos.le (sq_nonneg (Real.log y)))
  unfold rankinFactor
  convert hh using 1 <;> ring

theorem threshold_eq_rankinFactor (C : ℝ) (n : ℕ) :
    threshold C n = C * rankinFactor (Real.log (Real.log n)) * Real.log n := by
  unfold threshold rankinFactor
  ring

theorem threshold_le_rankinEnvelope {C U : ℝ} (hC : 0 ≤ C) {n : ℕ}
    (hn : 1 < (n : ℝ)) (hloglog : Real.exp 2 ≤ Real.log (Real.log n))
    (hlogU : Real.log n ≤ U) :
    threshold C n ≤ C * U * rankinFactor (Real.log U) := by
  have hlogn := Real.log_pos hn
  have hv := Real.log_le_log hlogn hlogU
  have hU := hloglog.trans hv
  have hfactor := rankinFactor_monotoneOn hloglog hU hv
  rw [threshold_eq_rankinFactor]
  calc
    _ ≤ (C * rankinFactor (Real.log U)) * U :=
      mul_le_mul (mul_le_mul_of_nonneg_left hfactor hC) hlogU hlogn.le
        (mul_nonneg hC (rankinFactor_nonneg hU))
    _ = _ := by ring

end

end Erdos4b
