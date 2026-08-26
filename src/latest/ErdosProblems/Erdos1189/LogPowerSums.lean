/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Asymptotics of sums of n/log n and n^2/log n by discrete differences.
Informal argument: summation preserves a negligible relative error with positive weights.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.LogPowerDifferences

namespace Erdos1189

open Finset Filter Asymptotics
open scoped Asymptotics

lemma logPower_ge_one {r n : ℕ} (hr : 1 ≤ r) (hn : 2 ≤ n) : 1 ≤ logPower r n := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans hn1)
  have hpow := le_self_pow₀ hn1.le (show r ≠ 0 by omega)
  apply (le_div_iff₀ (Real.log_pos hn1)).mpr
  linarith

lemma sum_logPower_tendsto_atTop {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun n => ∑ i ∈ range n, logPower r i) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (Nat.ceil b + 2)] with n hn
  have hn2 : 2 ≤ n := by omega
  have hlow : (n : ℝ) - 2 ≤ ∑ i ∈ range n, logPower r i := by
    calc
      _ = ∑ i ∈ Ico 2 n, (1 : ℝ) := by simp [Nat.cast_sub hn2]
      _ ≤ ∑ i ∈ Ico 2 n, logPower r i := sum_le_sum fun i hi =>
        logPower_ge_one hr (mem_Ico.mp hi).1
      _ ≤ ∑ i ∈ range n, logPower r i := sum_le_sum_of_subset_of_nonneg
        (fun i hi => mem_range.mpr (mem_Ico.mp hi).2) (fun _ _ _ => logPower_nonneg _ _)
  have hceil := Nat.le_ceil b
  have hn' : (Nat.ceil b : ℝ) + 2 ≤ n := by exact_mod_cast hn
  linarith

lemma sum_range_equivalent {f g : ℕ → ℝ} (hfg : f ~[atTop] g)
    (hg : ∀ n, 0 ≤ g n) (hgt : Tendsto (fun n => ∑ i ∈ range n, g i) atTop atTop) :
    (fun n => ∑ i ∈ range n, f i) ~[atTop] (fun n => ∑ i ∈ range n, g i) := by
  rw [IsEquivalent]
  change (fun n => (∑ i ∈ range n, f i) - ∑ i ∈ range n, g i) =o[atTop]
    (fun n => ∑ i ∈ range n, g i)
  simpa only [Pi.sub_apply, sum_sub_distrib] using hfg.isLittleO.sum_range hg hgt

lemma sum_equivalent_of_difference_limit {f g : ℕ → ℝ} {c : ℝ}
    (hc : c ≠ 0) (hf0 : f 0 = 0) (hg : ∀ n, 0 ≤ g n)
    (hgn : ∀ᶠ n in atTop, g n ≠ 0)
    (hgt : Tendsto (fun n => ∑ i ∈ range n, g i) atTop atTop)
    (hlim : Tendsto (fun n => (f (n + 1) - f n) / g n) atTop (nhds c)) :
    (fun n => ∑ i ∈ range n, g i) ~[atTop] (fun n => f n / c) := by
  have hdiff : (fun n => (f (n + 1) - f n) / c) ~[atTop] g := by
    apply (isEquivalent_iff_tendsto_one hgn).mpr
    have ht := hlim.div_const c
    rw [div_self hc] at ht
    convert ht using 1
    funext n
    simp only [Pi.div_apply]
    ring
  have hsum := (sum_range_equivalent hdiff hg hgt).symm
  apply hsum.congr_right
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [← sum_div, Finset.sum_range_sub, hf0, sub_zero]

theorem sum_logPower_one_equivalent :
    (fun n => ∑ i ∈ range n, logPower 1 i) ~[atTop] (fun n => logPower 2 n / 2) := by
  apply sum_equivalent_of_difference_limit (by norm_num) (by simp [logPower])
    (logPower_nonneg 1) _ (sum_logPower_tendsto_atTop (by norm_num))
    tendsto_logPower_two_difference
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (logPower_ge_one (by norm_num) hn))

theorem sum_logPower_two_equivalent :
    (fun n => ∑ i ∈ range n, logPower 2 i) ~[atTop] (fun n => logPower 3 n / 3) := by
  apply sum_equivalent_of_difference_limit (by norm_num) (by simp [logPower])
    (logPower_nonneg 2) _ (sum_logPower_tendsto_atTop (by norm_num))
    tendsto_logPower_three_difference
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (logPower_ge_one (by norm_num) hn))

end Erdos1189
