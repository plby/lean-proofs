/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The logarithmic size estimate and the negligible losses in the frame count.
Informal argument: n(x) is asymptotic to (tau/2) x^2/log x, so log n(x) ~ 2 log x.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingEntropyLower

namespace Erdos1189

open Filter

lemma countingSize_pos (x : ℝ) : 0 < countingSize x := by
  dsimp [countingSize]
  omega

lemma countingSize_log_ratio :
    Tendsto (fun x : ℝ => Real.log (countingSize x) / Real.log x) atTop (nhds 2) := by
  have hc : tau / 2 ≠ 0 := (div_pos tau_pos (by norm_num)).ne'
  have hlog := (Real.continuousAt_log hc).tendsto.comp countingSize_asymptotic
  have hsmall := hlog.mul Real.tendsto_log_atTop.inv_tendsto_atTop
  have hloglog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    Real.tendsto_log_atTop
  have ht := (hsmall.add_const 2).sub hloglog
  simp only [mul_zero, zero_add, sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hn0 : (countingSize x : ℝ) ≠ 0 := by exact_mod_cast (countingSize_pos x).ne'
  have hq0 : realLogPower 2 x ≠ 0 := div_ne_zero (pow_ne_zero _ hx0) hl0
  dsimp only [Function.comp_apply, Pi.div_apply, Pi.inv_apply, id_eq]
  rw [Real.log_div hn0 hq0, realLogPower, Real.log_div (pow_ne_zero _ hx0) hl0,
    Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  field_simp
  ring

lemma countingWeight_log_over_entropyScale :
    Tendsto (fun x : ℝ => (simpsonWeight (countingInteger x) : ℝ) *
      Real.log (countingSize x) / entropyScale x) atTop (nhds 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have ht := (countingWeight_asymptotic.mul countingSize_log_ratio).mul hlog
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  dsimp [realLogPower, entropyScale]
  field_simp

lemma counting_loss_over_entropyScale :
    Tendsto (fun x : ℝ => (simpsonWeight (countingInteger x) : ℝ) *
      (Real.log 2 + 2 * Real.log (countingSize x)) / entropyScale x) atTop (nhds 0) := by
  have ht := (countingWeight_over_entropyScale.const_mul (Real.log 2)).add
    (countingWeight_log_over_entropyScale.const_mul 2)
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun x => by dsimp only; ring

/-- The finite frame count attains the sharp entropy lower constant along its sizes. -/
theorem counting_frame_log_eventually_lower {b : ℝ} (hb : b < tau ^ 2 / 3) :
    ∀ᶠ x : ℝ in atTop,
      b < Real.log (irreducibleCount (countingSize x)) / entropyScale x := by
  obtain ⟨b', hbb', hb'⟩ := exists_between hb
  filter_upwards [countingEntropy_eventually_lower hb',
    (tendsto_order.mp counting_loss_over_entropyScale).2 (b' - b) (sub_pos.mpr hbb'),
    eventually_gt_atTop (coordinateScore 7 0), eventually_gt_atTop (1 : ℝ)]
      with x hx hsmall hx7 hx1
  have h := div_le_div_of_nonneg_right (countingEntropy_lower_count hx7)
    (entropyScale_pos hx1).le
  rw [sub_div] at h
  linarith

end Erdos1189
