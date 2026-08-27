/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBernoulliConcentration

/-! # Actual weighted uniform-hypergraph sampling probabilities -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def uniformWeightNormalizer
    {V : Type*} [Fintype V] [DecidableEq V] (w : V → ℝ≥0) (r : ℕ) : ℝ≥0 :=
  ∑ S ∈ (univ : Finset V).powersetCard r, ∏ v ∈ S, w v

theorem uniformWeightNormalizer_lower
    {V : Type*} [Fintype V] [DecidableEq V] (w : V → ℝ≥0) (a : ℝ≥0) (r : ℕ)
    (hw : ∀ v, a ≤ w v) :
    (Nat.choose (Fintype.card V) r : ℝ≥0) * a ^ r ≤ uniformWeightNormalizer w r := by
  calc
    _ = ∑ _S ∈ (univ : Finset V).powersetCard r, a ^ r := by
      simp [card_powersetCard]
    _ ≤ _ := by
      apply sum_le_sum
      intro S hS
      rw [← (mem_powersetCard.mp hS).2]
      simpa using prod_le_prod' (fun v (_hv : v ∈ S) ↦ hw v)

theorem uniformWeightNormalizer_pos
    {V : Type*} [Fintype V] [DecidableEq V] (w : V → ℝ≥0) (a : ℝ≥0) (r : ℕ)
    (ha : 0 < a) (hw : ∀ v, a ≤ w v) (hr : r ≤ Fintype.card V) :
    0 < uniformWeightNormalizer w r := by
  apply lt_of_lt_of_le _ (uniformWeightNormalizer_lower w a r hw)
  exact mul_pos (by exact_mod_cast Nat.choose_pos hr) (pow_pos ha r)

def uniformEdgeProbability
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → ℝ≥0) (k : ℕ) (E : Finset V) : ℝ≥0 :=
  (∏ v ∈ E, w v) / uniformWeightNormalizer w (k - 1)

theorem uniformEdgeProbability_le
    {V : Type*} [Fintype V] [DecidableEq V] (w : V → ℝ≥0) (a : ℝ≥0)
    {k : ℕ} (hk : 1 ≤ k) (ha : 0 < a) (hlo : ∀ v, a ≤ w v)
    (hhi : ∀ v, w v ≤ 2 * a) {E : Finset V} (hE : E.card = k) :
    uniformEdgeProbability w k E ≤
      2 ^ k * a / (Nat.choose (Fintype.card V) (k - 1) : ℝ≥0) := by
  have hr : k - 1 ≤ Fintype.card V := (Nat.sub_le k 1).trans
    (hE.symm.trans_le (card_le_univ E))
  have hC : (0 : ℝ≥0) < Nat.choose (Fintype.card V) (k - 1) := by
    exact_mod_cast Nat.choose_pos hr
  have hprod : (∏ v ∈ E, w v) ≤ (2 * a) ^ k := by
    simpa only [prod_const, hE] using prod_le_prod' (fun v (_hv : v ∈ E) ↦ hhi v)
  calc
    _ ≤ (2 * a) ^ k /
        ((Nat.choose (Fintype.card V) (k - 1) : ℝ≥0) * a ^ (k - 1)) :=
      div_le_div₀ zero_le hprod (mul_pos hC (pow_pos ha _))
        (uniformWeightNormalizer_lower w a (k - 1) hlo)
    _ = _ := by
      rw [mul_pow, show k = (k - 1) + 1 by omega, pow_succ a]
      simp only [Nat.add_sub_cancel]
      field_simp

theorem uniformEdgeProbability_root_le
    {V : Type*} [Fintype V] [DecidableEq V] (w : V → ℝ≥0) (a : ℝ≥0)
    {k : ℕ} (ha : 0 < a) (hlo : ∀ v, a ≤ w v) (hhi : ∀ v, w v ≤ 2 * a)
    {E : Finset V} (hE : E.card = k) {v : V} (hv : v ∈ E) :
    uniformEdgeProbability w k E ≤
      w v * 2 ^ (k - 1) / (Nat.choose (Fintype.card V) (k - 1) : ℝ≥0) := by
  have hr : k - 1 ≤ Fintype.card V := (Nat.sub_le k 1).trans
    (hE.symm.trans_le (card_le_univ E))
  have hC : (0 : ℝ≥0) < Nat.choose (Fintype.card V) (k - 1) := by
    exact_mod_cast Nat.choose_pos hr
  have hprod : (∏ u ∈ E, w u) ≤ w v * (2 * a) ^ (k - 1) := by
    rw [← mul_prod_erase _ _ hv]
    apply mul_le_mul_of_nonneg_left _ zero_le
    simpa only [prod_const, card_erase_of_mem hv, hE] using
      prod_le_prod' (fun u (_hu : u ∈ E.erase v) ↦ hhi u)
  calc
    _ ≤ (w v * (2 * a) ^ (k - 1)) /
        ((Nat.choose (Fintype.card V) (k - 1) : ℝ≥0) * a ^ (k - 1)) :=
      div_le_div₀ zero_le hprod (mul_pos hC (pow_pos ha _))
        (uniformWeightNormalizer_lower w a (k - 1) hlo)
    _ = _ := by rw [mul_pow]; field_simp

end

end Erdos207
