/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.LayerSelection
import ErdosProblems.Erdos874.RestrictedSums

/-!
# Erdős 874: an elementary universal upper bound

This file records the elementary packing estimate used before the deeper
Deshouillers--Freiman structure theorem.  If `K = A.card`, the sharp elementary
lower bound

`r * (K - r) + 1 ≤ #(restrictedSumset r A)`

is summed over all positive layers.  Admissibility packs those layers into
the integer interval `[1, K * N]`.  The resulting exact finite inequality is

`K ^ 3 + 5 * K ≤ 6 * K * N`.

For nonempty `A`, cancellation gives `K ^ 2 + 5 ≤ 6 * N`.  This deliberately
coarse `sqrt 6` bound is already strong enough to turn the `1.44` small-layer
estimate from `LayerSelection` into the convenient capacity bound
`4 * #s^A < 9 * N`.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The exact polynomial sum -/

private lemma six_mul_sum_range_int_mul_sub (K : ℤ) (n : ℕ) :
    6 * ∑ r ∈ Finset.range n, (r : ℤ) * (K - (r : ℤ)) =
      (n : ℤ) * ((n : ℤ) - 1) * (3 * K - (2 * (n : ℤ) - 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

/-- Exact evaluation of the sum of all elementary layer lower bounds. -/
lemma six_mul_sum_layer_lower_bounds (K : ℕ) :
    6 * ∑ r ∈ Finset.Icc 1 K, (r * (K - r) + 1) = K ^ 3 + 5 * K := by
  have hcast_sub : ∀ r ∈ Finset.Icc 1 K,
      (((r * (K - r) + 1 : ℕ) : ℤ)) =
        (r : ℤ) * ((K : ℤ) - (r : ℤ)) + 1 := by
    intro r hr
    simp only [Finset.mem_Icc] at hr
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hr.2]
    norm_num
  have hinterval : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hpoly :
      (6 : ℤ) * ∑ r ∈ Finset.Icc 1 K,
          ((r : ℤ) * ((K : ℤ) - (r : ℤ)) + 1) =
        (K : ℤ) ^ 3 + 5 * (K : ℤ) := by
    have hmain := six_mul_sum_range_int_mul_sub (K : ℤ) (K + 1)
    rw [hinterval, Finset.sum_Ico_eq_sub _ (by omega : 1 ≤ K + 1)]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero, zero_add]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast at hmain ⊢
    calc
      6 * (∑ x ∈ Finset.range (K + 1),
          (x : ℤ) * ((K : ℤ) - (x : ℤ)) + ((K : ℤ) + 1) - 1) =
          6 * (∑ x ∈ Finset.range (K + 1),
            (x : ℤ) * ((K : ℤ) - (x : ℤ))) + 6 * (K : ℤ) := by ring
      _ = (K : ℤ) ^ 3 + 5 * (K : ℤ) := by rw [hmain]; ring
  have hcast_sum :
      ((∑ r ∈ Finset.Icc 1 K, (r * (K - r) + 1) : ℕ) : ℤ) =
        ∑ r ∈ Finset.Icc 1 K,
          ((r : ℤ) * ((K : ℤ) - (r : ℤ)) + 1) := by
    push_cast
    apply Finset.sum_congr rfl
    intro r hr
    exact hcast_sub r hr
  have hcast_identity :
      (((6 * ∑ r ∈ Finset.Icc 1 K, (r * (K - r) + 1) : ℕ) : ℕ) : ℤ) =
        (((K ^ 3 + 5 * K : ℕ) : ℕ) : ℤ) := by
    calc
      (((6 * ∑ r ∈ Finset.Icc 1 K, (r * (K - r) + 1) : ℕ) : ℕ) : ℤ) =
          (6 : ℤ) *
            ((∑ r ∈ Finset.Icc 1 K, (r * (K - r) + 1) : ℕ) : ℤ) := by
              push_cast
              rfl
      _ = (6 : ℤ) * ∑ r ∈ Finset.Icc 1 K,
          ((r : ℤ) * ((K : ℤ) - (r : ℤ)) + 1) := by rw [hcast_sum]
      _ = (K : ℤ) ^ 3 + 5 * (K : ℤ) := hpoly
      _ = (((K ^ 3 + 5 * K : ℕ) : ℕ) : ℤ) := by
        push_cast
        rfl
  exact_mod_cast hcast_identity

/-! ## Packing all positive layers -/

/-- The sum of the elementary lower bounds for all positive layers is at
most the capacity `K * N` of the containing interval. -/
lemma sum_layer_lower_bounds_le
    {N : ℕ} {A : Finset ℤ} (hA : IsBoundedAdmissible N A) :
    ∑ r ∈ Finset.Icc 1 A.card, (r * (A.card - r) + 1) ≤ A.card * N := by
  calc
    ∑ r ∈ Finset.Icc 1 A.card, (r * (A.card - r) + 1) ≤
        ∑ r ∈ Finset.Icc 1 A.card, (restrictedSumset r A).card := by
      apply Finset.sum_le_sum
      intro r hr
      have hrle : r ≤ A.card := (Finset.mem_Icc.mp hr).2
      exact card_restrictedSumset_lower_bound A r hrle
    _ ≤ A.card * N := sum_card_restrictedSumset_Icc_le hA (by omega)

/-- Cubic form of Straus's elementary all-layer packing bound.  This version
also covers the empty set without a separate hypothesis. -/
theorem straus_cubic_upper
    {N : ℕ} {A : Finset ℤ} (hA : IsBoundedAdmissible N A) :
    A.card ^ 3 + 5 * A.card ≤ 6 * (A.card * N) := by
  rw [← six_mul_sum_layer_lower_bounds A.card]
  exact Nat.mul_le_mul_left 6 (sum_layer_lower_bounds_le hA)

/-- The exact nonempty-set consequence of the cubic packing estimate. -/
theorem straus_square_add_five_le
    {N : ℕ} {A : Finset ℤ} (hA : IsBoundedAdmissible N A)
    (hcard : 0 < A.card) :
    A.card ^ 2 + 5 ≤ 6 * N := by
  have hcubic := straus_cubic_upper hA
  have hfactor :
      A.card * (A.card ^ 2 + 5) ≤ A.card * (6 * N) := by
    simpa [pow_succ, mul_add, mul_assoc, mul_left_comm, mul_comm] using hcubic
  exact Nat.le_of_mul_le_mul_left hfactor hcard

/-- Coarser square-only form, convenient for callers that do not need the
strict additive saving. -/
theorem straus_prebound
    {N : ℕ} {A : Finset ℤ} (hA : IsBoundedAdmissible N A) :
    A.card ^ 2 ≤ 6 * N := by
  by_cases hcard : A.card = 0
  · simp [hcard]
  · exact (Nat.le_add_right _ 5).trans
      (straus_square_add_five_le hA (Nat.pos_of_ne_zero hcard))

/-! ## The selected-layer capacity used by the structural argument -/

private lemma four_mul_product_le_square {s K : ℕ} (hs : s ≤ K) :
    4 * (s * (K - s)) ≤ K ^ 2 := by
  have hsquare : (0 : ℤ) ≤ ((K : ℤ) - 2 * (s : ℤ)) ^ 2 := sq_nonneg _
  exact_mod_cast (by
    nlinarith : (4 : ℤ) * ((s : ℤ) * ((K : ℤ) - (s : ℤ))) ≤ (K : ℤ) ^ 2)

/-- A DF95-selected layer satisfying the `1.44` bound has fewer than
`9N/4` elements.  The proof uses only bounded admissibility and the preceding
universal `sqrt 6` estimate. -/
theorem four_mul_restrictedSumset_card_lt_nine_mul
    {N s : ℕ} {A : Finset ℤ} (hA : IsBoundedAdmissible N A)
    (hsmall :
      25 * (restrictedSumset s A).card < 36 * s * (A.card - s)) :
    4 * (restrictedSumset s A).card < 9 * N := by
  let L := (restrictedSumset s A).card
  have hprodpos : 0 < s * (A.card - s) := by
    have hrhs : 0 < 36 * (s * (A.card - s)) := by
      simpa only [mul_assoc] using
        (lt_of_le_of_lt (Nat.zero_le (25 * (restrictedSumset s A).card)) hsmall)
    exact Nat.pos_of_mul_pos_left hrhs
  have hs : s ≤ A.card := by
    by_contra h
    have : A.card - s = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [this] at hprodpos
    simp at hprodpos
  have hcard : 0 < A.card := by
    have hsubpos : 0 < A.card - s := by
      by_contra h
      have hz : A.card - s = 0 := by omega
      simp [hz] at hprodpos
    omega
  have hproduct := four_mul_product_le_square hs
  have hsquare := straus_square_add_five_le hA hcard
  have hsmallZ :
      (25 : ℤ) * (L : ℤ) < 36 * (s : ℤ) * ((A.card - s : ℕ) : ℤ) := by
    exact_mod_cast hsmall
  have hproductZ :
      (4 : ℤ) * ((s : ℤ) * ((A.card - s : ℕ) : ℤ)) ≤ (A.card : ℤ) ^ 2 := by
    exact_mod_cast hproduct
  have hsquareZ : (A.card : ℤ) ^ 2 + 5 ≤ 6 * (N : ℤ) := by
    exact_mod_cast hsquare
  have hNpos : 0 < N := by
    have : 0 < 6 * N := lt_of_lt_of_le (by omega : 0 < A.card ^ 2 + 5) hsquare
    omega
  have htargetZ : (4 : ℤ) * (L : ℤ) < 9 * (N : ℤ) := by
    nlinarith
  exact_mod_cast htargetZ

end

end Erdos874
