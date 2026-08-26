/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The exact asymptotic size of the optimal arithmetic frames.
Informal source: BBMST equation (21); the infinite exponent sum is justified
by the proved logarithmic summable envelope.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingDomination
import ErdosProblems.Erdos1189.ScaledPrimeMoments
import Mathlib.Analysis.Normed.Group.Tannery

namespace Erdos1189

open Finset Filter

lemma countingSize_normalized_tsum (x : ℝ) :
    (∑' e : ℕ, realPrimeWeightSum (x * logIncrement e) / realLogPower 2 x) =
      ((countingSize x : ℝ) - 1) / realLogPower 2 x := by
  rw [tsum_eq_sum (s := range (Nat.ceil x)) (fun e he => by
    rw [realPrimeWeightSum_exponent_zero (by simpa only [mem_range, not_lt] using he), zero_div])]
  rw [← sum_div, countingSize_real_eq, add_sub_cancel_left]

lemma tendsto_inv_realLogPower_two :
    Tendsto (fun x : ℝ => 1 / realLogPower 2 x) atTop (nhds 0) := by
  have ht := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.mul
    ((tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).inv_tendsto_atTop)
  simp only [mul_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun x => by
    dsimp [realLogPower]
    simp only [pow_two, mul_inv, div_eq_mul_inv, inv_inv]
    ring

/-- The frame size is asymptotic to `(tau/2) x^2/log x`. -/
theorem countingSize_asymptotic :
    Tendsto (fun x : ℝ => (countingSize x : ℝ) / realLogPower 2 x)
      atTop (nhds (tau / 2)) := by
  obtain ⟨C, _, hdom⟩ := exists_counting_size_domination
  have ht := tendsto_tsum_of_dominated_convergence
    (summable_logIncrement_log_weight.mul_left C)
    (fun e : ℕ => scaled_prime_weight_sum_ratio (logIncrement_pos e))
    ((eventually_ge_atTop (2 : ℝ)).mono fun x hx => hdom x hx)
  have hsum : (∑' e : ℕ, logIncrement e ^ 2 / 2) = tau / 2 := by
    rw [tsum_div_const, ← tau_eq_tsum_logIncrement]
  rw [hsum] at ht
  have ht' : Tendsto (fun x : ℝ => ((countingSize x : ℝ) - 1) / realLogPower 2 x)
      atTop (nhds (tau / 2)) := by
    apply ht.congr'
    exact Eventually.of_forall countingSize_normalized_tsum
  have hfinal := ht'.add tendsto_inv_realLogPower_two
  simp only [add_zero] at hfinal
  apply hfinal.congr'
  exact Eventually.of_forall fun x => by
    dsimp only
    ring

lemma realLogPower_two_tendsto : Tendsto (realLogPower 2) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans hx)
  apply (le_div_iff₀ (Real.log_pos hx)).mpr
  change x * Real.log x ≤ x ^ 2
  have hmul := mul_le_mul_of_nonneg_left hlog (zero_lt_one.trans hx).le
  nlinarith

lemma countingSize_real_tendsto :
    Tendsto (fun x : ℝ => (countingSize x : ℝ)) atTop atTop := by
  have hc : 0 < tau / 4 := div_pos tau_pos (by norm_num)
  have ht := realLogPower_two_tendsto.atTop_mul_const hc
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [(tendsto_order.mp countingSize_asymptotic).1 (tau / 4) (by linarith [tau_pos]),
    eventually_gt_atTop (1 : ℝ)] with x hratio hx
  have hq : 0 < realLogPower 2 x := div_pos (sq_pos_of_pos (zero_lt_one.trans hx)) (Real.log_pos hx)
  have h := (lt_div_iff₀ hq).mp hratio
  nlinarith

lemma countingSize_tendsto : Tendsto countingSize atTop atTop :=
  tendsto_natCast_atTop_iff.mp countingSize_real_tendsto

lemma countingSize_mono : Monotone countingSize := by
  intro x y hxy
  rw [countingSize_eq, countingSize_eq]
  apply Nat.add_le_add_left
  exact sum_le_sum_of_subset_of_nonneg (countingCoordinates_mono hxy) (fun _ _ _ => Nat.zero_le _)

end Erdos1189
