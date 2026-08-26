/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B1SecondMoment

/-! # Exact periodic counts and reciprocal mass of coprime integers -/

namespace Erdos822

open scoped BigOperators

def coprimeIndicator (Q n : ℕ) : ℝ := if Q.Coprime n then 1 else 0

def coprimeInterval (Q L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter Q.Coprime

theorem sum_coprimeIndicator_period (Q : ℕ) :
    ∑ n ∈ Finset.range Q, coprimeIndicator Q n = (Nat.totient Q : ℝ) := by
  simp [coprimeIndicator, Nat.totient_eq_card_coprime]

theorem sum_coprimeIndicator_full_periods (Q m : ℕ) :
    ∑ n ∈ Finset.range (m * Q), coprimeIndicator Q n =
      (m : ℝ) * Nat.totient Q := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have hperiod :
        (∑ n ∈ Finset.range Q, coprimeIndicator Q (m * Q + n)) = Nat.totient Q := by
      calc
        (∑ n ∈ Finset.range Q, coprimeIndicator Q (m * Q + n)) =
            ∑ n ∈ Finset.range Q, coprimeIndicator Q n := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [coprimeIndicator, Nat.add_comm, Nat.coprime_add_mul_right_right]
        _ = Nat.totient Q := sum_coprimeIndicator_period Q
    rw [hperiod]
    push_cast
    ring

theorem sum_coprimeIndicator_range_lower {Q T : ℕ} (hQ : 0 < Q) :
    (T : ℝ) * ((Nat.totient Q : ℝ) / Q) - Q ≤
      ∑ n ∈ Finset.range T, coprimeIndicator Q n := by
  have hmono :
      (∑ n ∈ Finset.range ((T / Q) * Q), coprimeIndicator Q n) ≤
        ∑ n ∈ Finset.range T, coprimeIndicator Q n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.div_mul_le_self T Q))
    intro n hn hnot
    unfold coprimeIndicator
    split_ifs <;> norm_num
  rw [sum_coprimeIndicator_full_periods] at hmono
  have hfloor := cast_div_sub_one_le_natCast_div (N := T) hQ
  have hmul := mul_le_mul_of_nonneg_right hfloor (show (0 : ℝ) ≤ Nat.totient Q by positivity)
  have hφ : (Nat.totient Q : ℝ) ≤ Q := by exact_mod_cast Nat.totient_le Q
  simp only [div_eq_mul_inv] at hmul ⊢
  nlinarith

theorem sum_coprimeIndicator_range_upper {Q T : ℕ} (hQ : 0 < Q) :
    (∑ n ∈ Finset.range T, coprimeIndicator Q n) ≤
      (T : ℝ) * ((Nat.totient Q : ℝ) / Q) + Q := by
  have hT : T ≤ (T / Q + 1) * Q := by
    have hmod := Nat.mod_lt T hQ
    have hdiv := Nat.div_add_mod T Q
    nlinarith
  have hmono :
      (∑ n ∈ Finset.range T, coprimeIndicator Q n) ≤
        ∑ n ∈ Finset.range ((T / Q + 1) * Q), coprimeIndicator Q n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hT)
    intro n hn hnot
    unfold coprimeIndicator
    split_ifs <;> norm_num
  rw [sum_coprimeIndicator_full_periods] at hmono
  have hfloor := natCast_div_le_cast_div T Q
  have hmul := mul_le_mul_of_nonneg_right hfloor (show (0 : ℝ) ≤ Nat.totient Q by positivity)
  have hφ : (Nat.totient Q : ℝ) ≤ Q := by exact_mod_cast Nat.totient_le Q
  push_cast at hmono
  simp only [div_eq_mul_inv] at hmul ⊢
  nlinarith

/-- Every interval has the expected totient-density count, with an error
of at most two periods. -/
theorem coprimeInterval_card_lower {Q L U : ℕ} (hQ : 0 < Q) (hLU : L ≤ U) :
    ((U : ℝ) - L) * ((Nat.totient Q : ℝ) / Q) - 2 * Q ≤
      (coprimeInterval Q L U).card := by
  have hcount : ((coprimeInterval Q L U).card : ℝ) =
      (∑ n ∈ Finset.range (U + 1), coprimeIndicator Q n) -
        ∑ n ∈ Finset.range (L + 1), coprimeIndicator Q n := by
    rw [← Finset.sum_Ico_eq_sub _ (show L + 1 ≤ U + 1 by omega)]
    have hI : Finset.Ico (L + 1) (U + 1) = Finset.Ioc L U := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hI]
    simp [coprimeInterval, coprimeIndicator]
  rw [hcount]
  have hupper := sum_coprimeIndicator_range_upper (T := L + 1) hQ
  have hlower := sum_coprimeIndicator_range_lower (T := U + 1) hQ
  push_cast at hupper hlower
  nlinarith

/-- A dyadic interval contributes a fixed positive reciprocal mass when
the period is small compared with its length. -/
theorem sum_inv_coprimeInterval_dyadic_lower
    {Q j : ℕ} {δ : ℝ} (hQ : 0 < Q)
    (_hδ : 0 ≤ δ) (hden : δ ≤ (Nat.totient Q : ℝ) / Q)
    (hsmall : 4 * (Q : ℝ) ≤ δ * (2 : ℝ) ^ j) :
    δ / 4 ≤ ∑ n ∈ coprimeInterval Q (2 ^ j) (2 ^ (j + 1)), (1 : ℝ) / n := by
  have hpow : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcount := coprimeInterval_card_lower hQ hpow
  have hwidth : ((2 ^ (j + 1) : ℕ) : ℝ) - (2 ^ j : ℕ) = (2 : ℝ) ^ j := by
    push_cast
    rw [pow_succ]
    ring
  rw [hwidth] at hcount
  have hdenMul := mul_le_mul_of_nonneg_left hden (show (0 : ℝ) ≤ (2 : ℝ) ^ j by positivity)
  have hcard : δ * (2 : ℝ) ^ j / 2 ≤
      (coprimeInterval Q (2 ^ j) (2 ^ (j + 1))).card := by nlinarith
  have hmass :
      ((coprimeInterval Q (2 ^ j) (2 ^ (j + 1))).card : ℝ) / (2 : ℝ) ^ (j + 1) ≤
        ∑ n ∈ coprimeInterval Q (2 ^ j) (2 ^ (j + 1)), (1 : ℝ) / n := by
    calc
      ((coprimeInterval Q (2 ^ j) (2 ^ (j + 1))).card : ℝ) / (2 : ℝ) ^ (j + 1) =
          ∑ _n ∈ coprimeInterval Q (2 ^ j) (2 ^ (j + 1)),
            (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by simp [div_eq_mul_inv]
      _ ≤ ∑ n ∈ coprimeInterval Q (2 ^ j) (2 ^ (j + 1)), (1 : ℝ) / n := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
        have hnpos : 0 < n := (by positivity : 0 < 2 ^ j).trans hn'.1
        exact one_div_le_one_div_of_le (by exact_mod_cast hnpos) (by exact_mod_cast hn'.2)
  calc
    δ / 4 = (δ * (2 : ℝ) ^ j / 2) / (2 : ℝ) ^ (j + 1) := by
      rw [pow_succ]
      field_simp
      norm_num
    _ ≤ ((coprimeInterval Q (2 ^ j) (2 ^ (j + 1))).card : ℝ) / (2 : ℝ) ^ (j + 1) :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ ≤ ∑ n ∈ coprimeInterval Q (2 ^ j) (2 ^ (j + 1)), (1 : ℝ) / n := hmass

end Erdos822
