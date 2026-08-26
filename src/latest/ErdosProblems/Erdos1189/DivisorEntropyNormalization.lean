/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Normalizing the score-cutoff optimization by an arbitrary weight budget.
Informal source: BBMST Lemma 6.3, with a dense integer-parameter cutoff.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingMass
import ErdosProblems.Erdos1189.CountingLower

namespace Erdos1189

open Filter

lemma preceding_weight_budget_ratio :
    Tendsto (fun k : ℕ => (k : ℝ) / realLogPower 2 (precedingFrameIndex k : ℝ))
      atTop (nhds (tau / 2)) := by
  have ht := (countingSize_asymptotic.comp precedingFrameIndex_real_tendsto).div
    precedingFrameSize_ratio (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hn0 : (countingSize (precedingFrameIndex k : ℝ) : ℝ) ≠ 0 := by
    exact_mod_cast (countingSize_pos (precedingFrameIndex k : ℝ)).ne'
  change (((countingSize (precedingFrameIndex k : ℝ) : ℝ) /
    realLogPower 2 (precedingFrameIndex k : ℝ)) /
      ((countingSize (precedingFrameIndex k : ℝ) : ℝ) / k)) = _
  field_simp

lemma preceding_log_parameter_ratio :
    Tendsto (fun k : ℕ => Real.log k / Real.log (precedingFrameIndex k : ℝ))
      atTop (nhds 2) := by
  have ht := precedingFrameSize_log_ratio.mul
    (countingSize_log_ratio.comp precedingFrameIndex_real_tendsto)
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [(countingSize_tendsto.comp precedingFrameIndex_real_tendsto).eventually
    (eventually_ge_atTop 2)] with k hk
  change 2 ≤ countingSize (precedingFrameIndex k : ℝ) at hk
  have hn : (1 : ℝ) < countingSize (precedingFrameIndex k : ℝ) := by
    exact_mod_cast (show 1 < countingSize (precedingFrameIndex k : ℝ) by omega)
  have hn0 := (Real.log_pos hn).ne'
  change Real.log k / Real.log (countingSize (precedingFrameIndex k : ℝ)) *
    (Real.log (countingSize (precedingFrameIndex k : ℝ)) / Real.log (precedingFrameIndex k : ℝ)) = _
  field_simp

lemma divisor_entropy_normalization_eq {x n : ℝ} (hx : 1 < x) (hn : 0 < n) :
    realLogPower 1 x * Real.sqrt (Real.log n) / Real.sqrt n =
      Real.sqrt (Real.log n / Real.log x) / Real.sqrt (n / realLogPower 2 x) := by
  have hx0 := (zero_lt_one.trans hx).ne'
  have hl := Real.log_pos hx
  have hl0 := hl.ne'
  have hsl0 := (Real.sqrt_pos.mpr hl).ne'
  have hsn0 := (Real.sqrt_pos.mpr hn).ne'
  rw [Real.sqrt_div' _ hl.le, Real.sqrt_div hn.le]
  unfold realLogPower
  rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq (zero_lt_one.trans hx).le, pow_one]
  field_simp
  rw [Real.sq_sqrt hl.le]
  ring

lemma divisor_entropy_normalization_constant :
    Real.sqrt 2 / Real.sqrt (tau / 2) = 2 / Real.sqrt tau := by
  rw [Real.sqrt_div tau_pos.le]
  have hs0 := (Real.sqrt_pos.mpr tau_pos).ne'
  field_simp
  norm_num

lemma divisor_entropy_normalization_limit :
    Tendsto (fun k : ℕ => realLogPower 1 (precedingFrameIndex k : ℝ) *
      Real.sqrt (Real.log k) / Real.sqrt k) atTop (nhds (2 / Real.sqrt tau)) := by
  have ht := preceding_log_parameter_ratio.sqrt.div preceding_weight_budget_ratio.sqrt
    (Real.sqrt_pos.mpr (show 0 < tau / 2 by linarith [tau_pos])).ne'
  rw [divisor_entropy_normalization_constant] at ht
  apply ht.congr'
  filter_upwards [precedingFrameIndex_real_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_ge_atTop 1] with k hj hk
  exact (divisor_entropy_normalization_eq hj
    (by exact_mod_cast (show 0 < k by omega))).symm

noncomputable def divisorEntropyBound (k : ℕ) : ℝ :=
  coordinateMass (countingCoordinates (precedingFrameIndex k : ℝ)) +
    ((k : ℝ) + 1 - countingSize (precedingFrameIndex k : ℝ)) / precedingFrameIndex k

lemma divisorEntropyBound_parameter_ratio :
    Tendsto (fun k : ℕ => divisorEntropyBound k / realLogPower 1 (precedingFrameIndex k : ℝ))
      atTop (nhds tau) := by
  have hr := (preceding_weight_budget_ratio.add
    (tendsto_inv_realLogPower_two.comp precedingFrameIndex_real_tendsto)).sub
      (countingSize_asymptotic.comp precedingFrameIndex_real_tendsto)
  simp only [add_zero, sub_self] at hr
  have ht := (countingMass_asymptotic.comp precedingFrameIndex_real_tendsto).add hr
  simp only [add_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun k => by
    dsimp only [Function.comp_apply, divisorEntropyBound, realLogPower]
    simp only [pow_one, pow_two, div_eq_mul_inv, mul_inv, inv_inv]
    ring

theorem divisorEntropyBound_asymptotic :
    Tendsto (fun k : ℕ => divisorEntropyBound k * Real.sqrt (Real.log k) / Real.sqrt k)
      atTop (nhds (2 * Real.sqrt tau)) := by
  have ht := divisorEntropyBound_parameter_ratio.mul divisor_entropy_normalization_limit
  have hc : tau * (2 / Real.sqrt tau) = 2 * Real.sqrt tau := by
    have hs0 := (Real.sqrt_pos.mpr tau_pos).ne'
    field_simp
    rw [Real.sq_sqrt tau_pos.le]
  rw [hc] at ht
  apply ht.congr'
  filter_upwards [precedingFrameIndex_real_tendsto.eventually
    (realLogPower_eventually_ne_zero 1)] with k hk
  field_simp

end Erdos1189
