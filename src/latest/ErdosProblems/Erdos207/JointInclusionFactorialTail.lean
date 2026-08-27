/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteProbability
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# Cardinality tails with separate witness order and degree cutoff

A residual star of degree at least `R` contains at least `R.choose s`
different `s`-edge witnesses.  Counting all witnesses in expectation and
applying Markov retains this denominator.  The joint-inclusion hypothesis
therefore needs only order `s`, even if the cutoff `R` is much larger.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- A binomial ratio is bounded without a factorial loss when the witness
order is at most half the degree cutoff. -/
lemma choose_ratio_le_two_mul_div_pow
    (m R s : ℕ) (hR : 0 < R) (hs : 2 * s ≤ R) :
    (m.choose s : ℝ≥0) / (R.choose s : ℝ≥0) ≤
      (2 * (m : ℝ≥0) / R) ^ s := by
  have hsR : s ≤ R := by omega
  have hchoose : (0 : ℝ≥0) < R.choose s := by
    exact_mod_cast Nat.choose_pos hsR
  have hbase : (0 : ℝ≥0) < (R + 1 - s : ℕ) := by
    exact_mod_cast (show 0 < R + 1 - s by omega)
  have hfac : (0 : ℝ≥0) < s.factorial := by
    exact_mod_cast Nat.factorial_pos s
  have hhalf : (R : ℝ≥0) / 2 ≤ (R + 1 - s : ℕ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    exact_mod_cast (show R ≤ (R + 1 - s) * 2 by omega)
  have hRreal : (0 : ℝ≥0) < R := by exact_mod_cast hR
  calc
    (m.choose s : ℝ≥0) / (R.choose s : ℝ≥0) ≤
        ((m : ℝ≥0) ^ s / s.factorial) / (R.choose s : ℝ≥0) :=
      div_le_div_of_nonneg_right (Nat.choose_le_pow_div s m) zero_le
    _ ≤ ((m : ℝ≥0) ^ s / s.factorial) /
        (((R + 1 - s : ℕ) : ℝ≥0) ^ s / s.factorial) :=
      div_le_div_of_nonneg_left zero_le (div_pos (pow_pos hbase _) hfac)
        (Nat.pow_le_choose s R)
    _ = ((m : ℝ≥0) / (R + 1 - s : ℕ)) ^ s := by
      rw [div_div_div_cancel_right₀ hfac.ne', div_pow]
    _ ≤ (2 * (m : ℝ≥0) / R) ^ s := by
      apply pow_le_pow_left'
      calc
        (m : ℝ≥0) / (R + 1 - s : ℕ) ≤ (m : ℝ≥0) / (R / 2) :=
          div_le_div_of_nonneg_left zero_le (div_pos hRreal (by norm_num)) hhalf
        _ = 2 * (m : ℝ≥0) / R := by
          rw [div_div_eq_mul_div, mul_comm]

namespace FiniteLaw

variable {Omega X : Type*} [Fintype Omega] [DecidableEq X]

lemma powersetCard_inter_eq_filter_subset
    (S Z : Finset X) (s : ℕ) :
    (S ∩ Z).powersetCard s =
      (S.powersetCard s).filter (fun Q ↦ Q ⊆ Z) := by
  ext Q
  simp only [mem_powersetCard, mem_filter, subset_inter_iff]
  tauto

/-- The factorial moment is exactly the sum of the witness probabilities. -/
theorem expectation_choose_card_inter_eq
    (L : FiniteLaw Omega) (selected : Omega → Finset X)
    (S : Finset X) (s : ℕ) :
    L.expectation (fun omega ↦
      ((S ∩ selected omega).card.choose s : ℝ≥0)) =
      ∑ Q ∈ S.powersetCard s,
        L.probability (fun omega ↦ Q ⊆ selected omega) := by
  classical
  have hcount (omega : Omega) :
      ((S ∩ selected omega).card.choose s : ℝ≥0) =
        ∑ Q ∈ S.powersetCard s,
          if Q ⊆ selected omega then (1 : ℝ≥0) else 0 := by
    rw [← card_powersetCard,
      powersetCard_inter_eq_filter_subset]
    simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  simp_rw [hcount]
  unfold expectation probability
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro Q _hQ
  apply sum_congr rfl
  intro omega _hOmega
  split_ifs <;> simp

/-- A uniform order-`s` joint-inclusion bound controls the order-`s`
factorial moment, without any assumption of independence. -/
theorem expectation_choose_card_inter_le
    (L : FiniteLaw Omega) (selected : Omega → Finset X)
    (S : Finset X) (s : ℕ) (b : ℝ≥0)
    (hjoint : ∀ Q ∈ S.powersetCard s,
      L.probability (fun omega ↦ Q ⊆ selected omega) ≤ b) :
    L.expectation (fun omega ↦
      ((S ∩ selected omega).card.choose s : ℝ≥0)) ≤
      (S.card.choose s : ℝ≥0) * b := by
  rw [L.expectation_choose_card_inter_eq selected S s]
  calc
    (∑ Q ∈ S.powersetCard s,
        L.probability (fun omega ↦ Q ⊆ selected omega)) ≤
        ∑ _Q ∈ S.powersetCard s, b := sum_le_sum hjoint
    _ = (S.card.choose s : ℝ≥0) * b := by simp

/-- Factorial-moment tail with a witness order independent of the cutoff. -/
theorem probability_card_inter_ge_le_factorialMoment
    (L : FiniteLaw Omega) (selected : Omega → Finset X)
    (S : Finset X) (s R : ℕ) (b : ℝ≥0) (hsR : s ≤ R)
    (hjoint : ∀ Q ∈ S.powersetCard s,
      L.probability (fun omega ↦ Q ⊆ selected omega) ≤ b) :
    L.probability (fun omega ↦ R ≤ (S ∩ selected omega).card) ≤
      (S.card.choose s : ℝ≥0) * b / (R.choose s : ℝ≥0) := by
  have hpos : (0 : ℝ≥0) < R.choose s := by
    exact_mod_cast Nat.choose_pos hsR
  calc
    L.probability (fun omega ↦ R ≤ (S ∩ selected omega).card) ≤
        L.probability (fun omega ↦
          (R.choose s : ℝ≥0) ≤
            ((S ∩ selected omega).card.choose s : ℝ≥0)) := by
      apply L.probability_mono
      intro omega hlarge
      exact_mod_cast Nat.choose_le_choose s hlarge
    _ ≤ L.expectation (fun omega ↦
        ((S ∩ selected omega).card.choose s : ℝ≥0)) /
          (R.choose s : ℝ≥0) :=
      L.probability_le_expectation_div _ hpos
    _ ≤ (S.card.choose s : ℝ≥0) * b / (R.choose s : ℝ≥0) := by
      exact div_le_div_of_nonneg_right
        (L.expectation_choose_card_inter_le selected S s b hjoint) zero_le

/-- The factorial tail in a form suitable for power-scale comparisons. -/
theorem probability_card_inter_ge_le_powerMoment
    (L : FiniteLaw Omega) (selected : Omega → Finset X)
    (S : Finset X) (s R : ℕ) (b : ℝ≥0)
    (hR : 0 < R) (hs : 2 * s ≤ R)
    (hjoint : ∀ Q ∈ S.powersetCard s,
      L.probability (fun omega ↦ Q ⊆ selected omega) ≤ b) :
    L.probability (fun omega ↦ R ≤ (S ∩ selected omega).card) ≤
      (2 * (S.card : ℝ≥0) / R) ^ s * b := by
  apply (L.probability_card_inter_ge_le_factorialMoment
    selected S s R b (by omega) hjoint).trans
  rw [mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right
    (choose_ratio_le_two_mul_div_pow S.card R s hR hs) zero_le

/-- One finite union bound gives simultaneous factorial-moment degree caps. -/
theorem probability_exists_card_inter_ge_le_factorialMoment
    {J : Type*} [DecidableEq J]
    (L : FiniteLaw Omega) (selected : Omega → Finset X)
    (tests : J → Finset X) (indices : Finset J)
    (s : ℕ) (R : J → ℕ) (b : ℝ≥0)
    (hsR : ∀ j ∈ indices, s ≤ R j)
    (hjoint : ∀ j ∈ indices, ∀ Q ∈ (tests j).powersetCard s,
      L.probability (fun omega ↦ Q ⊆ selected omega) ≤ b) :
    L.probability (fun omega ↦ ∃ j ∈ indices,
      R j ≤ ((tests j) ∩ selected omega).card) ≤
      ∑ j ∈ indices,
        ((tests j).card.choose s : ℝ≥0) * b / ((R j).choose s : ℝ≥0) := by
  apply (L.probability_exists_le indices
    (fun j omega ↦ R j ≤ ((tests j) ∩ selected omega).card)).trans
  apply sum_le_sum
  intro j hj
  exact L.probability_card_inter_ge_le_factorialMoment
    selected (tests j) s (R j) b (hsR j hj) (hjoint j hj)

end FiniteLaw

end

end Erdos207
