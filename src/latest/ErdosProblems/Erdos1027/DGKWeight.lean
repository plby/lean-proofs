/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1027.Basic

/-!
# Dyadic-weight bridges for the DGK argument

The decision-tree part of the proof uses the integral numerator
`Tree.scaledWeight n H`.  The probabilistic argument naturally uses
`\sum E \in H, 2 ^ (-|E|)`.  Importantly, the bridge below is an inequality
and therefore does not require the edges to have cardinality at most `n`:
when `n < |E|`, the truncated natural subtraction in `scaledWeight` merely
replaces the Boolean-weight summand by a larger one.
-/

namespace Erdos1027.DGKWeight

open scoped BigOperators

abbrev Hypergraph (α : Type*) := Tree.Hypergraph α

/-- The usual Boolean weight, with exact rational values. -/
def booleanWeightQ {α : Type*} [DecidableEq α] (H : Hypergraph α) : ℚ :=
  ∑ E ∈ H, (2 : ℚ) ^ (-(E.card : ℤ))

/-- The usual Boolean weight, regarded as a real number. -/
noncomputable def booleanWeightR {α : Type*} [DecidableEq α] (H : Hypergraph α) : ℝ :=
  ∑ E ∈ H, (2 : ℝ) ^ (-(E.card : ℤ))

/-- The doubled weight `q(H) = \sum_E 2^(1-|E|)` used by DGK. -/
def qWeightQ {α : Type*} [DecidableEq α] (H : Hypergraph α) : ℚ :=
  2 * booleanWeightQ H

/-- The real-valued version of the doubled DGK weight. -/
noncomputable def qWeightR {α : Type*} [DecidableEq α] (H : Hypergraph α) : ℝ :=
  2 * booleanWeightR H

/-- A Boolean-weight summand is bounded by its truncated common-denominator
counterpart.  This is the key fact that removes any `E.card ≤ n` hypothesis. -/
lemma booleanTermQ_le_scaledTerm (n k : ℕ) :
    (2 : ℚ) ^ (-(k : ℤ)) ≤
      ((2 ^ (n - k) : ℕ) : ℚ) / (2 : ℚ) ^ n := by
  rw [zpow_neg, zpow_natCast]
  by_cases hk : k ≤ n
  · rw [show ((2 ^ (n - k) : ℕ) : ℚ) = (2 : ℚ) ^ (n - k) by norm_cast]
    have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - k) * (2 : ℚ) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    rw [hpow]
    apply le_of_eq
    field_simp
  · have hnk : n ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
    rw [Nat.sub_eq_zero_of_le hnk]
    norm_num only [pow_zero, Nat.cast_one, one_div]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by positivity : (0 : ℚ) < (2 : ℚ) ^ n)
        (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hnk))

/-- Real analogue of `booleanTermQ_le_scaledTerm`. -/
lemma booleanTermR_le_scaledTerm (n k : ℕ) :
    (2 : ℝ) ^ (-(k : ℤ)) ≤
      ((2 ^ (n - k) : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  rw [zpow_neg, zpow_natCast]
  by_cases hk : k ≤ n
  · rw [show ((2 ^ (n - k) : ℕ) : ℝ) = (2 : ℝ) ^ (n - k) by norm_cast]
    have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - k) * (2 : ℝ) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    rw [hpow]
    apply le_of_eq
    field_simp
  · have hnk : n ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hk)
    rw [Nat.sub_eq_zero_of_le hnk]
    norm_num only [pow_zero, Nat.cast_one, one_div]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnk))

/-- The rational Boolean weight is at most the normalized integral weight,
without any upper bound on edge sizes. -/
lemma booleanWeightQ_le_scaledWeight_div {α : Type*} [DecidableEq α]
    (n : ℕ) (H : Hypergraph α) :
    booleanWeightQ H ≤ (Tree.scaledWeight n H : ℚ) / (2 : ℚ) ^ n := by
  rw [booleanWeightQ, Tree.scaledWeight, Nat.cast_sum, Finset.sum_div]
  exact Finset.sum_le_sum fun E hE ↦ booleanTermQ_le_scaledTerm n E.card

/-- The corresponding real-valued normalized-weight bound. -/
lemma booleanWeightR_le_scaledWeight_div {α : Type*} [DecidableEq α]
    (n : ℕ) (H : Hypergraph α) :
    booleanWeightR H ≤ (Tree.scaledWeight n H : ℝ) / (2 : ℝ) ^ n := by
  rw [booleanWeightR, Tree.scaledWeight, Nat.cast_sum, Finset.sum_div]
  exact Finset.sum_le_sum fun E hE ↦ booleanTermR_le_scaledTerm n E.card

lemma booleanWeightQ_nonneg {α : Type*} [DecidableEq α] (H : Hypergraph α) :
    0 ≤ booleanWeightQ H := by
  exact Finset.sum_nonneg fun _ _ ↦ zpow_nonneg (by norm_num : (0 : ℚ) ≤ 2) _

lemma booleanWeightR_nonneg {α : Type*} [DecidableEq α] (H : Hypergraph α) :
    0 ≤ booleanWeightR H := by
  exact Finset.sum_nonneg fun _ _ ↦ zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _

/-- An integral scaled-weight budget controls the exact rational Boolean
weight even for edges larger than the scale `n`. -/
lemma booleanWeightQ_le_of_scaledWeight_le {α : Type*} [DecidableEq α]
    {D n : ℕ} {H : Hypergraph α}
    (hweight : Tree.scaledWeight n H ≤ D * 2 ^ n) :
    booleanWeightQ H ≤ D := by
  refine (booleanWeightQ_le_scaledWeight_div n H).trans ?_
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ n)).2
  exact_mod_cast hweight

/-- Real version of `booleanWeightQ_le_of_scaledWeight_le`. -/
lemma booleanWeightR_le_of_scaledWeight_le {α : Type*} [DecidableEq α]
    {D n : ℕ} {H : Hypergraph α}
    (hweight : Tree.scaledWeight n H ≤ D * 2 ^ n) :
    booleanWeightR H ≤ D := by
  refine (booleanWeightR_le_scaledWeight_div n H).trans ?_
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).2
  exact_mod_cast hweight

/-- A scaled budget `D` gives DGK doubled rational weight at most `2D`. -/
lemma qWeightQ_le_two_mul_of_scaledWeight_le {α : Type*} [DecidableEq α]
    {D n : ℕ} {H : Hypergraph α}
    (hweight : Tree.scaledWeight n H ≤ D * 2 ^ n) :
    qWeightQ H ≤ 2 * D := by
  exact mul_le_mul_of_nonneg_left
    (booleanWeightQ_le_of_scaledWeight_le hweight) (by norm_num)

/-- A scaled budget `D` gives DGK doubled real weight at most `2D`. -/
lemma qWeightR_le_two_mul_of_scaledWeight_le {α : Type*} [DecidableEq α]
    {D n : ℕ} {H : Hypergraph α}
    (hweight : Tree.scaledWeight n H ≤ D * 2 ^ n) :
    qWeightR H ≤ 2 * D := by
  exact mul_le_mul_of_nonneg_left
    (booleanWeightR_le_of_scaledWeight_le hweight) (by norm_num)

lemma qWeightQ_nonneg {α : Type*} [DecidableEq α] (H : Hypergraph α) :
    0 ≤ qWeightQ H :=
  mul_nonneg (by norm_num) (booleanWeightQ_nonneg H)

lemma qWeightR_nonneg {α : Type*} [DecidableEq α] (H : Hypergraph α) :
    0 ≤ qWeightR H :=
  mul_nonneg (by norm_num) (booleanWeightR_nonneg H)

end Erdos1027.DGKWeight
