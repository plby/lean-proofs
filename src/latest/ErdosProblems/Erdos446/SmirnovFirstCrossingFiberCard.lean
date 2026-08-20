/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovFirstCrossingCode

/-!
# Erdős Problem 446: exact cardinalities of first-crossing fibers

The coordinates not frozen by a first-crossing code split into two classes.
Labels after the crossing label may use the crossing slot itself, while labels
before it must start in the next slot.  This file evaluates the resulting
Cartesian product exactly.
-/

namespace Erdos446

open Finset

/-- Among the unfrozen coordinates of a first-crossing code, the number whose
label is strictly after the crossing label. -/
noncomputable def crossingSuffixAfterCount {k u v : ℕ}
    (F : FailedWord k u v) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun i ↦
    (firstCrossingCode F).entries i = none ∧
      (firstCrossingCode F).label < i).card

theorem crossingSuffixAfterCount_le {k u v : ℕ}
    (F : FailedWord k u v) :
    crossingSuffixAfterCount F ≤ k - (u + firstFailedSlot u F.1) := by
  rw [← card_firstCrossingCode_none F]
  exact Finset.card_le_card (by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.1)

theorem card_crossingCodeLetter_eq_ite {k u v V : ℕ}
    (F : FailedWord k u v) (hvV : v ≤ V)
    (hrV : firstFailedSlot u F.1 ≤ V) (i : Fin k) :
    Fintype.card (CrossingCodeLetter V (firstCrossingCode F) i) =
      if (firstCrossingCode F).entries i = none then
        if (firstCrossingCode F).label < i then
          V - (firstFailedSlot u F.1 - 1)
        else V - firstFailedSlot u F.1
      else 1 := by
  by_cases hnone : (firstCrossingCode F).entries i = none
  · rw [if_pos hnone]
    by_cases hafter : (firstCrossingCode F).label < i
    · rw [if_pos hafter]
      exact card_crossingCodeLetter_none_after F (by omega) hafter hnone
    · rw [if_neg hafter]
      exact card_crossingCodeLetter_none_before F hrV (le_of_not_gt hafter) hnone
  · rw [if_neg hnone]
    exact card_crossingCodeLetter_some F hvV hnone

theorem card_wordsWithCrossingCode_eq_suffix_powers {k u v V : ℕ}
    (F : FailedWord k u v) (hvV : v ≤ V)
    (hrV : firstFailedSlot u F.1 ≤ V) :
    (wordsWithCrossingCode V (firstCrossingCode F)).card =
      (V - (firstFailedSlot u F.1 - 1)) ^ crossingSuffixAfterCount F *
        (V - firstFailedSlot u F.1) ^
          (k - (u + firstFailedSlot u F.1) - crossingSuffixAfterCount F) := by
  rw [card_wordsWithCrossingCode_eq_prod]
  simp_rw [card_crossingCodeLetter_eq_ite F hvV hrV]
  simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
  have hafter :
      (((Finset.univ : Finset (Fin k)).filter fun i ↦
          (firstCrossingCode F).entries i = none).filter fun i ↦
            (firstCrossingCode F).label < i).card = crossingSuffixAfterCount F := by
    rw [crossingSuffixAfterCount]
    congr 1
    ext i
    simp
  have hbefore :
      (((Finset.univ : Finset (Fin k)).filter fun i ↦
          (firstCrossingCode F).entries i = none).filter fun i ↦
            ¬ (firstCrossingCode F).label < i).card =
        k - (u + firstFailedSlot u F.1) - crossingSuffixAfterCount F := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := ((Finset.univ : Finset (Fin k)).filter fun i ↦
        (firstCrossingCode F).entries i = none))
      (p := fun i ↦ (firstCrossingCode F).label < i)
    have hnone : ((Finset.univ : Finset (Fin k)).filter fun i ↦
        (firstCrossingCode F).entries i = none).card =
          k - (u + firstFailedSlot u F.1) := card_firstCrossingCode_none F
    rw [hafter, hnone] at hpartition
    omega
  rw [hafter, hbefore]

end Erdos446
