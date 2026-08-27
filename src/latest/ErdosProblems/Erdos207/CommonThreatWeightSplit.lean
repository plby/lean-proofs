/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatSwap

/-! # The full common-threat extension weight splits into three proved cases -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def commonThreatExceptionalWeight
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H : Finset W) (p : ℝ≥0) : ℝ≥0 := by
  classical
  exact ∑ w : CommonThreatWitness F G T T',
    if H = ∅ ∧ w.first.erase T = w.second.erase T' then p ^ (w.remainder \ H).card else 0

theorem commonThreatGoodWeight_swap_eq
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H : Finset W) (r s : ℕ) (p : ℝ≥0) :
    commonThreatGoodWeight G F T' T H s r p =
      ∑ w : CommonThreatWitness F G T T',
        if H ⊆ w.remainder ∧ (w.swap.exposureCode H).IsGood H s r then
          p ^ (w.remainder \ H).card else 0 := by
  classical
  calc
    _ = ∑ z : CommonThreatWitness G F T' T,
        if H ⊆ z.remainder ∧ (z.exposureCode H).IsGood H s r then
          p ^ (z.remainder \ H).card else 0 := by
      rw [commonThreatGoodWeight, sum_filter]
    _ = ∑ w : CommonThreatWitness F G T T',
        if H ⊆ w.swap.remainder ∧ (w.swap.exposureCode H).IsGood H s r then
          p ^ (w.swap.remainder \ H).card else 0 :=
      ((CommonThreatWitness.swapEquiv F G T T').sum_comp _).symm
    _ = _ := by simp only [CommonThreatWitness.swap_remainder]

theorem extensionWeight_commonThreat_le_split
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H : Finset W) (r s : ℕ) (p : ℝ≥0)
    (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2) :
    extensionWeight (fun w : CommonThreatWitness F G T T' ↦ w.remainder) (fun _ ↦ p) H ≤
      commonThreatGoodWeight F G T T' H r s p + commonThreatGoodWeight G F T' T H s r p +
        commonThreatExceptionalWeight F G T T' H p := by
  classical
  rw [commonThreatGoodWeight_swap_eq F G T T' H r s p]
  simp only [extensionWeight, setWeight, prod_const, commonThreatGoodWeight,
    commonThreatExceptionalWeight, sum_filter]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro w _
  by_cases hH : H ⊆ w.remainder
  · simp only [hH, if_true, true_and]
    rcases w.good_or_swap_good_or_equal_remainders H r s hH
      (hF w.first w.first_mem) (hG w.second w.second_mem) with h | h | h
    · rw [if_pos h]
      exact (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
    · rw [if_pos h]
      exact (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)
    · have hex : H = ∅ ∧ w.first.erase T = w.second.erase T' := ⟨h.1, h.2.2⟩
      rw [if_pos hex]
      exact le_add_of_nonneg_left zero_le
  · simp only [hH, if_false, false_and]
    exact zero_le

end

end Erdos207
