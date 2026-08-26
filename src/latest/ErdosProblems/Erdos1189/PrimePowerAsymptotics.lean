/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The first two prime moments, with their exact leading constants.
Informal argument: the proved prime number theorem and finite partial summation.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.PrimePartialSummation
import ErdosProblems.Erdos1189.LogPowerSums

namespace Erdos1189

open Finset Filter Asymptotics
open scoped Asymptotics

lemma logPower_eventually_ne_zero (r : ℕ) : ∀ᶠ n in atTop, logPower r n ≠ 0 := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact div_ne_zero (pow_ne_zero _ hn0)
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'

lemma tendsto_ratio_of_scaled_equivalent {f g : ℕ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hgn : ∀ᶠ n in atTop, g n ≠ 0) (hfg : f ~[atTop] (fun n => g n / c)) :
    Tendsto (fun n => f n / g n) atTop (nhds (1 / c)) := by
  have hgc : ∀ᶠ n in atTop, g n / c ≠ 0 := hgn.mono fun n hn => div_ne_zero hn hc
  have ht := ((isEquivalent_iff_tendsto_one hgc).mp hfg).div_const c
  apply ht.congr'
  filter_upwards [hgn] with n hn
  dsimp only [Pi.div_apply]
  field_simp

lemma sum_primeCounting_ratio :
    Tendsto (fun n => (∑ i ∈ range n, (Nat.primeCounting i : ℝ)) / logPower 2 n)
      atTop (nhds (1 / 2)) := by
  have hpc : (fun n : ℕ => (Nat.primeCounting n : ℝ)) ~[atTop] logPower 1 := by
    change (fun n : ℕ => (Nat.primeCounting n : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ 1 / Real.log n)
    simpa only [pow_one] using primeCounting_equivalent
  have hs := (sum_range_equivalent hpc (logPower_nonneg 1)
    (sum_logPower_tendsto_atTop (by norm_num))).trans sum_logPower_one_equivalent
  exact tendsto_ratio_of_scaled_equivalent (by norm_num) (logPower_eventually_ne_zero 2) hs

lemma sum_weighted_primeCounting_ratio :
    Tendsto (fun n => (∑ i ∈ range n, (Nat.primeCounting i : ℝ) * i) / logPower 3 n)
      atTop (nhds (1 / 3)) := by
  have hm : (fun n : ℕ => (Nat.primeCounting n : ℝ) * n) ~[atTop]
      (fun n : ℕ => (n : ℝ) / Real.log n * n) :=
    primeCounting_equivalent.mul IsEquivalent.refl
  have hpc : (fun n : ℕ => (Nat.primeCounting n : ℝ) * n) ~[atTop] logPower 2 := by
    apply hm.congr_right
    exact Eventually.of_forall fun n => by dsimp [logPower]; ring
  have hs := (sum_range_equivalent hpc (logPower_nonneg 2)
    (sum_logPower_tendsto_atTop (by norm_num))).trans sum_logPower_two_equivalent
  exact tendsto_ratio_of_scaled_equivalent (by norm_num) (logPower_eventually_ne_zero 3) hs

lemma primeCounting_endpoint_ratio (r : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ r * Nat.primeCounting n / logPower (r + 1) n)
      atTop (nhds 1) := by
  apply BoundedGaps.unconditional_ordinaryPrimeNumberTheorem.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hl0 : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  dsimp [logPower]
  rw [pow_succ]
  field_simp

lemma sum_primeCounting_over_logPower_three :
    Tendsto (fun n => (∑ i ∈ range n, (Nat.primeCounting i : ℝ)) / logPower 3 n)
      atTop (nhds 0) := by
  have ht := sum_primeCounting_ratio.mul
    (tendsto_natCast_atTop_atTop.inv_tendsto_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hl0 : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  dsimp [logPower]
  field_simp

theorem prime_sum_ratio :
    Tendsto (fun n => (∑ p ∈ Nat.primesLE n, (p : ℝ)) / logPower 2 n)
      atTop (nhds (1 / 2)) := by
  have ht := (primeCounting_endpoint_ratio 1).sub sum_primeCounting_ratio
  norm_num only [pow_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at ht
  apply ht.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [prime_partial_summation (fun p => (p : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, mul_one, sub_div]

theorem prime_square_sum_ratio :
    Tendsto (fun n => (∑ p ∈ Nat.primesLE n, (p : ℝ) ^ 2) / logPower 3 n)
      atTop (nhds (1 / 3)) := by
  have ht := ((primeCounting_endpoint_ratio 2).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul sum_weighted_primeCounting_ratio)).sub
    sum_primeCounting_over_logPower_three
  have ht' : Tendsto (fun n : ℕ =>
      (n : ℝ) ^ 2 * Nat.primeCounting n / logPower 3 n -
        2 * ((∑ i ∈ range n, (Nat.primeCounting i : ℝ) * i) / logPower 3 n) -
          (∑ i ∈ range n, (Nat.primeCounting i : ℝ)) / logPower 3 n)
      atTop (nhds (1 / 3)) := by norm_num at ht; exact ht
  apply ht'.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [prime_power_sum]
    have hsum : (∑ i ∈ range n, (Nat.primeCounting i : ℝ) *
        (((i : ℝ) + 1) ^ 2 - (i : ℝ) ^ 2)) =
          2 * (∑ i ∈ range n, (Nat.primeCounting i : ℝ) * i) +
            ∑ i ∈ range n, (Nat.primeCounting i : ℝ) := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      ring
    rw [hsum]
    ring

lemma tendsto_ratio_logPower_succ_zero {f : ℕ → ℝ} {r : ℕ} {a : ℝ}
    (h : Tendsto (fun n => f n / logPower r n) atTop (nhds a)) :
    Tendsto (fun n => f n / logPower (r + 1) n) atTop (nhds 0) := by
  have ht := h.mul (tendsto_natCast_atTop_atTop.inv_tendsto_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0))
  simp only [mul_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun n => by
    dsimp [logPower]
    rw [pow_succ]
    ring

lemma primeCounting_over_logPower_two :
    Tendsto (fun n => (Nat.primeCounting n : ℝ) / logPower 2 n) atTop (nhds 0) := by
  have h := primeCounting_endpoint_ratio 0
  simp only [pow_zero, one_mul, zero_add] at h
  exact tendsto_ratio_logPower_succ_zero h

theorem prime_weight_sum_ratio :
    Tendsto (fun n => (∑ p ∈ Nat.primesLE n, ((p : ℝ) - 1)) / logPower 2 n)
      atTop (nhds (1 / 2)) := by
  have ht := prime_sum_ratio.sub primeCounting_over_logPower_two
  simp only [sub_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one,
      Nat.primesLE_card_eq_primeCounting, sub_div]

theorem prime_weight_square_sum_ratio :
    Tendsto (fun n => (∑ p ∈ Nat.primesLE n, ((p : ℝ) - 1) ^ 2) / logPower 3 n)
      atTop (nhds (1 / 3)) := by
  have hs : Tendsto (fun n => (∑ p ∈ Nat.primesLE n, (p : ℝ)) / logPower 3 n)
      atTop (nhds 0) := tendsto_ratio_logPower_succ_zero prime_sum_ratio
  have hp : Tendsto (fun n => (Nat.primeCounting n : ℝ) / logPower 3 n)
      atTop (nhds 0) := tendsto_ratio_logPower_succ_zero primeCounting_over_logPower_two
  have ht := (prime_square_sum_ratio.sub ((tendsto_const_nhds (x := (2 : ℝ))).mul hs)).add hp
  simp only [mul_zero, sub_zero, add_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    have heq : (∑ p ∈ Nat.primesLE n, ((p : ℝ) - 1) ^ 2) =
        (∑ p ∈ Nat.primesLE n, (p : ℝ) ^ 2) -
          2 * (∑ p ∈ Nat.primesLE n, (p : ℝ)) + Nat.primeCounting n := by
      have hcard : (∑ p ∈ Nat.primesLE n, (1 : ℝ)) = Nat.primeCounting n := by
        simp [Nat.primesLE_card_eq_primeCounting]
      rw [← hcard, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro p _
      ring
    rw [heq]
    ring

end Erdos1189
