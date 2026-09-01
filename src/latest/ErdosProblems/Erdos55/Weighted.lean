/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.FiniteSums

/-!
# Weighted subset-sum counting for Erdős Problem 55

This file proves the exponential-base version of CFP Lemma 3.4.  It is stated
for a finite set whose members are already truncated at `m`; this is exactly
the finite form used after intersecting one hue of the eventual coloring with
`[1,m]`.
-/

open scoped BigOperators

namespace Erdos55

/-- **CFP Lemma 3.4 (base `e`).**  The number of positive subset-sum values
at most `m` is bounded by a weighted product. -/
theorem card_subsetSums_Icc_le_weightedProduct (S : Finset ℕ) {m q : ℕ}
    (hq : 0 < q) :
    (((subsetSumValues S).filter fun n ↦ 1 ≤ n ∧ n ≤ m).card : ℝ) ≤
      Real.exp ((m : ℝ) / q) *
        ∏ a ∈ S, (1 + Real.exp (-(a : ℝ) / q)) := by
  classical
  let represented := (subsetSumValues S).filter fun n ↦ 1 ≤ n ∧ n ≤ m
  have hwitness (n : represented) :
      ∃ t : Finset ℕ, t ⊆ S ∧ (∑ a ∈ t, a) = n := by
    have hn : (n : ℕ) ∈ subsetSumValues S := (Finset.mem_filter.mp n.2).1
    exact mem_subsetSumValues.mp hn
  let witness : represented → Finset ℕ := fun n ↦ (hwitness n).choose
  have hwitness_subset (n : represented) : witness n ⊆ S :=
    (hwitness n).choose_spec.1
  have hwitness_sum (n : represented) : (∑ a ∈ witness n, a) = n :=
    (hwitness n).choose_spec.2
  let witnessEmbedding : represented ↪ Finset ℕ :=
    ⟨witness, by
      intro n k hnk
      apply Subtype.ext
      calc
        (n : ℕ) = ∑ a ∈ witness n, a := (hwitness_sum n).symm
        _ = ∑ a ∈ witness k, a := by rw [hnk]
        _ = (k : ℕ) := hwitness_sum k⟩
  let chosen : Finset (Finset ℕ) := Finset.univ.map witnessEmbedding
  have hchosen_card : chosen.card = represented.card := by simp [chosen]
  have hchosen_subset : chosen ⊆ S.powerset := by
    intro t ht
    obtain ⟨n, -, rfl⟩ := Finset.mem_map.mp ht
    exact Finset.mem_powerset.mpr (hwitness_subset n)
  let weight (a : ℕ) : ℝ := Real.exp (-(a : ℝ) / q)
  let term (t : Finset ℕ) : ℝ :=
    Real.exp ((m : ℝ) / q) * ∏ a ∈ t, weight a
  have hterm_one (t : Finset ℕ) (ht : t ∈ chosen) : 1 ≤ term t := by
    obtain ⟨n, -, htn⟩ := Finset.mem_map.mp ht
    subst t
    have hnle : (n : ℕ) ≤ m := (Finset.mem_filter.mp n.2).2.2
    have hsumcast : (∑ a ∈ witness n, (a : ℝ)) = (n : ℝ) := by
      simpa only [Nat.cast_sum] using
        congrArg (fun z : ℕ ↦ (z : ℝ)) (hwitness_sum n)
    dsimp [term, weight]
    rw [← Real.exp_sum]
    rw [← Real.exp_add]
    apply Real.one_le_exp
    change 0 ≤ (m : ℝ) / q + ∑ x ∈ witness n, -(x : ℝ) / q
    rw [← Finset.sum_div, Finset.sum_neg_distrib, hsumcast]
    have hnleR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnle
    have hqR : 0 ≤ (q : ℝ) := by positivity
    have heq : (m : ℝ) / q + -(n : ℝ) / q = ((m : ℝ) - n) / q := by ring
    rw [heq]
    exact div_nonneg (sub_nonneg.mpr hnleR) hqR
  calc
    (((subsetSumValues S).filter fun n ↦ 1 ≤ n ∧ n ≤ m).card : ℝ)
        = (chosen.card : ℝ) := by rw [hchosen_card]
    _ = ∑ t ∈ chosen, (1 : ℝ) := by simp
    _ ≤ ∑ t ∈ chosen, term t := by
      exact Finset.sum_le_sum fun t ht ↦ hterm_one t ht
    _ ≤ ∑ t ∈ S.powerset, term t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hchosen_subset
      intro t _ _
      positivity
    _ = Real.exp ((m : ℝ) / q) *
        ∑ t ∈ S.powerset, ∏ a ∈ t, weight a := by
      rw [Finset.mul_sum]
    _ = Real.exp ((m : ℝ) / q) *
        ∏ a ∈ S, (1 + Real.exp (-(a : ℝ) / q)) := by
      rw [Finset.prod_one_add]

/-- The product in CFP Lemma 3.4 is at most the exponential of the sum of
its weights. -/
theorem weightedProduct_le_exp_sum (S : Finset ℕ) {m q : ℕ} :
    Real.exp ((m : ℝ) / q) *
        ∏ a ∈ S, (1 + Real.exp (-(a : ℝ) / q)) ≤
      Real.exp ((m : ℝ) / q + ∑ a ∈ S, Real.exp (-(a : ℝ) / q)) := by
  calc
    Real.exp ((m : ℝ) / q) *
        ∏ a ∈ S, (1 + Real.exp (-(a : ℝ) / q))
        ≤ Real.exp ((m : ℝ) / q) *
            Real.exp (∑ a ∈ S, Real.exp (-(a : ℝ) / q)) := by
          gcongr
          apply Real.prod_one_add_le_exp_sum
          intro a
          positivity
    _ = Real.exp ((m : ℝ) / q + ∑ a ∈ S, Real.exp (-(a : ℝ) / q)) := by
      rw [Real.exp_add]

/-- Combined weighted subset-sum estimate. -/
theorem card_subsetSums_Icc_le_exp (S : Finset ℕ) {m q : ℕ} (hq : 0 < q) :
    (((subsetSumValues S).filter fun n ↦ 1 ≤ n ∧ n ≤ m).card : ℝ) ≤
      Real.exp ((m : ℝ) / q + ∑ a ∈ S, Real.exp (-(a : ℝ) / q)) :=
  (card_subsetSums_Icc_le_weightedProduct S hq).trans
    (weightedProduct_le_exp_sum S)

end Erdos55
