/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SlotSum

/-!
# Erdős Problem 446: close-pair weight of a vector block family

The slot-array estimate is translated back to Ford's arithmetic weight
`sum_a W(a)/a` on the squarefree block family.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem blockChoice_closeWeight_eq_selection
    (M k : ℕ) (b : ℕ → ℕ) :
    (∑ T ∈ blockChoiceTuples M k b,
        selectionWeight (choiceUnion T) *
          ((subsetClosePairs (choiceUnion T)).card : ℝ)) =
      ∑ S ∈ blockSelectionSets M k b,
        selectionWeight S * ((subsetClosePairs S).card : ℝ) := by
  rw [← image_choiceUnion_eq_blockSelectionSets M k b,
    Finset.sum_image (choiceUnion_injOn M k b)]

theorem blockSelection_closeWeight_eq_blockFamily
    (M k : ℕ) (b : ℕ → ℕ) :
    (∑ S ∈ blockSelectionSets M k b,
        selectionWeight S * ((subsetClosePairs S).card : ℝ)) =
      ∑ a ∈ blockFamily M k b, (closePairCount a : ℝ) / a := by
  rw [blockFamily, Finset.sum_image (selectionProduct_injOn M k b)]
  apply Finset.sum_congr rfl
  intro S hS
  rw [selectionWeight_eq_inv_product,
    ← closePairCount_primeSelectionProduct
      (fun p hp ↦ prime_of_mem_selection hS hp)]
  push_cast
  ring

theorem blockChoice_closeWeight_eq_blockFamily
    (M k : ℕ) (b : ℕ → ℕ) :
    (∑ T ∈ blockChoiceTuples M k b,
        selectionWeight (choiceUnion T) *
          ((subsetClosePairs (choiceUnion T)).card : ℝ)) =
      ∑ a ∈ blockFamily M k b, (closePairCount a : ℝ) / a := by
  rw [blockChoice_closeWeight_eq_selection,
    blockSelection_closeWeight_eq_blockFamily]

/-- Explicit largest-difference bound for the arithmetic close-pair weight of
one vector class. -/
theorem blockFamily_closeWeight_upper
    {N M k : ℕ} {b : ℕ → ℕ}
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin k, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ))
    {H : ℝ} (hH : 0 ≤ H)
    (hmass : ∀ i : Fin k, primeBlockMass (M + i) ≤ H) :
    (∏ i : Fin k, ((b i).factorial : ℝ)) *
        (∑ a ∈ blockFamily M k b, (closePairCount a : ℝ) / a) ≤
      (2 : ℝ) ^ slotCount k b * H ^ slotCount k b +
      ∑ s : BlockSlot k b,
        (2 : ℝ) ^ (slotCount k b +
          ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) *
          (H ^ (slotCount k b - 1) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) := by
  calc
    (∏ i : Fin k, ((b i).factorial : ℝ)) *
        (∑ a ∈ blockFamily M k b, (closePairCount a : ℝ) / a) =
      (∏ i : Fin k, ((b i).factorial : ℝ)) *
        (∑ T ∈ blockChoiceTuples M k b,
          selectionWeight (choiceUnion T) *
            ((subsetClosePairs (choiceUnion T)).card : ℝ)) := by
      rw [blockChoice_closeWeight_eq_blockFamily]
    _ ≤ ∑ z ∈ closeSlotConfigurations M k b,
        slotConfigurationWeight z :=
      blockFactorial_mul_closeChoiceWeight_le_slotSum M k b
    _ ≤ _ := closeSlotSum_upper hN hendpoint hprime hH hmass

/-- Exact reciprocal-block-mass version of the vector-class close-pair
estimate.  This is the form used in the sharp asymptotic assembly. -/
theorem blockFamily_closeWeight_upper_exact
    {N M k : ℕ} {b : ℕ → ℕ}
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin k, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ)) :
    (∏ i : Fin k, ((b i).factorial : ℝ)) *
        (∑ a ∈ blockFamily M k b, (closePairCount a : ℝ) / a) ≤
      (2 : ℝ) ^ slotCount k b *
        (∏ s : BlockSlot k b, primeBlockMass (M + s.1)) +
      ∑ s : BlockSlot k b,
        (2 : ℝ) ^ (slotCount k b +
          ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) *
          ((∏ t : {t : BlockSlot k b // t ≠ s},
              primeBlockMass (M + t.1.1)) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) := by
  calc
    (∏ i : Fin k, ((b i).factorial : ℝ)) *
        (∑ a ∈ blockFamily M k b, (closePairCount a : ℝ) / a) =
      (∏ i : Fin k, ((b i).factorial : ℝ)) *
        (∑ T ∈ blockChoiceTuples M k b,
          selectionWeight (choiceUnion T) *
            ((subsetClosePairs (choiceUnion T)).card : ℝ)) := by
      rw [blockChoice_closeWeight_eq_blockFamily]
    _ ≤ ∑ z ∈ closeSlotConfigurations M k b,
        slotConfigurationWeight z :=
      blockFactorial_mul_closeChoiceWeight_le_slotSum M k b
    _ ≤ _ := closeSlotSum_upper_exact hN hendpoint hprime

end Erdos446
