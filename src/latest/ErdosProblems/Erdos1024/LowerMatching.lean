/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic

/-!
# The matching calculation in the Phelps--Rödl lower bound

The link of a vertex in a linear triple system is a matching.  This file
contains the exact finite averaging estimate used in the weighted
independent-set argument.  It deliberately uses only natural-number sums;
no probability or limiting binomial estimate is hidden in the statement.
-/

open scoped BigOperators

namespace Erdos1024
namespace Lower

variable {V : Type*} [DecidableEq V]

/-- The number of members of `M` which are wholly selected by `S`. -/
def coveredPairs (M : Finset (Finset V)) (S : Finset V) : ℕ :=
  (M.filter (· ⊆ S)).card

@[simp] lemma coveredPairs_eq_zero {M : Finset (Finset V)} {S : Finset V} :
    coveredPairs M S = 0 ↔ ∀ e ∈ M, ¬ e ⊆ S := by
  simp [coveredPairs, Finset.card_eq_zero]

lemma coveredPairs_le_card (M : Finset (Finset V)) (S : Finset V) :
    coveredPairs M S ≤ M.card := by
  exact Finset.card_filter_le _ _

lemma sum_indicator_superset {J e : Finset V} (heJ : e ⊆ J) :
    ∑ S ∈ J.powerset, (if e ⊆ S then (1 : ℕ) else 0) =
      2 ^ (J.card - e.card) := by
  classical
  calc
    ∑ S ∈ J.powerset, (if e ⊆ S then (1 : ℕ) else 0) =
        ((J.powerset).filter (e ⊆ ·)).card := by
          exact Finset.sum_boole (e ⊆ ·) J.powerset
    _ = (Finset.Icc e J).card := by
      congr 1
      ext S
      simp [Finset.mem_Icc, and_comm]
    _ = 2 ^ (J.card - e.card) := by
      exact Finset.card_Icc_finset heJ

/-- Double-count incidences `(pair, subset containing the pair)`. -/
lemma sum_coveredPairs {J : Finset V} {M : Finset (Finset V)}
    (hMJ : ∀ e ∈ M, e ⊆ J) (hM2 : ∀ e ∈ M, e.card = 2) :
    ∑ S ∈ J.powerset, coveredPairs M S = M.card * 2 ^ (J.card - 2) := by
  classical
  have hcover : ∀ S, coveredPairs M S =
      ∑ e ∈ M, (if e ⊆ S then (1 : ℕ) else 0) := by
    intro S
    unfold coveredPairs
    exact (Finset.sum_boole (· ⊆ S) M).symm
  simp_rw [hcover]
  rw [Finset.sum_comm]
  calc
    ∑ e ∈ M, ∑ S ∈ J.powerset, (if e ⊆ S then (1 : ℕ) else 0) =
        ∑ e ∈ M, 2 ^ (J.card - e.card) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [sum_indicator_superset (hMJ e he)]
    _ = ∑ _e ∈ M, 2 ^ (J.card - 2) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [hM2 e he]
    _ = M.card * 2 ^ (J.card - 2) := by simp

lemma mul_min_ge {B k j : ℕ} (hBk : B ≤ k) (hjk : j ≤ k) :
    B * j ≤ k * min j B := by
  by_cases hjB : j ≤ B
  · rw [min_eq_left hjB]
    exact Nat.mul_le_mul_right j hBk
  · rw [min_eq_right (Nat.le_of_not_ge hjB)]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left B hjk

/-- If a matching has at least `B` pairs, truncating the number of selected
pairs at `B` loses at most a factor four in its powerset average. -/
lemma four_mul_sum_min_coveredPairs
    {J : Finset V} {M : Finset (Finset V)} {B : ℕ}
    (hB : 0 < B) (hBM : B ≤ M.card)
    (hMJ : ∀ e ∈ M, e ⊆ J) (hM2 : ∀ e ∈ M, e.card = 2) :
    B * 2 ^ J.card ≤
      4 * ∑ S ∈ J.powerset, min (coveredPairs M S) B := by
  classical
  have hMpos : 0 < M.card := hB.trans_le hBM
  have hpoint : ∀ S ∈ J.powerset,
      B * coveredPairs M S ≤ M.card * min (coveredPairs M S) B := by
    intro S _
    exact mul_min_ge hBM (coveredPairs_le_card M S)
  have hsum0 :
      (∑ S ∈ J.powerset, B * coveredPairs M S) ≤
        ∑ S ∈ J.powerset, M.card * min (coveredPairs M S) B :=
    Finset.sum_le_sum fun S hS ↦ hpoint S hS
  have hsum :
      B * (∑ S ∈ J.powerset, coveredPairs M S) ≤
        M.card * ∑ S ∈ J.powerset, min (coveredPairs M S) B := by
    simpa only [Finset.mul_sum] using hsum0
  have hdouble := sum_coveredPairs hMJ hM2
  rw [hdouble] at hsum
  have hJ2 : 2 ≤ J.card := by
    obtain ⟨e, heM⟩ := Finset.card_pos.mp hMpos
    exact (hM2 e heM) ▸ Finset.card_le_card (hMJ e heM)
  have hpow : 4 * 2 ^ (J.card - 2) = 2 ^ J.card := by
    calc
      4 * 2 ^ (J.card - 2) = 2 ^ 2 * 2 ^ (J.card - 2) := by norm_num
      _ = 2 ^ (2 + (J.card - 2)) := (pow_add 2 2 (J.card - 2)).symm
      _ = 2 ^ J.card := by rw [Nat.add_sub_of_le hJ2]
  have hcancel :
      B * 2 ^ (J.card - 2) ≤
        ∑ S ∈ J.powerset, min (coveredPairs M S) B := by
    apply Nat.le_of_mul_le_mul_left
    · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum
    · exact hMpos
  calc
    B * 2 ^ J.card = 4 * (B * 2 ^ (J.card - 2)) := by
      rw [← hpow]
      ac_rfl
    _ ≤ 4 * ∑ S ∈ J.powerset, min (coveredPairs M S) B :=
      Nat.mul_le_mul_left 4 hcancel

end Lower
end Erdos1024

#print axioms Erdos1024.Lower.four_mul_sum_min_coveredPairs
