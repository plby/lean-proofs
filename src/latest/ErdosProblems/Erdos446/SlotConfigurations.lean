/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.OrderedSlots

/-!
# Erdős Problem 446: finite close slot configurations

The ordered prime arrays from `OrderedSlots` take values in finite prime
blocks.  We package them as a finite dependent function type, transfer the
close-divisor condition to products over the two bit masks, and compare the
weighted source sum with the sum over all (possibly repeated-prime) slot
configurations.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- A prime chosen from the block prescribed by every slot. -/
abbrev SlotPrimeArray (M k : ℕ) (b : ℕ → ℕ) :=
  ∀ s : BlockSlot k b, ↥(primeBlock (M + s.1))

/-- A finite ordered prime array and two membership bits at every slot. -/
abbrev SlotConfiguration (M k : ℕ) (b : ℕ → ℕ) :=
  SlotPrimeArray M k b × (BlockSlot k b → Bool × Bool)

/-- The ordered configuration, with each prime bundled with its block
membership proof. -/
noncomputable def boundedOrderedConfiguration {M k : ℕ} {b : ℕ → ℕ}
    (z : CloseBlockChoice M k b × BlockPermutations k b) :
    SlotConfiguration M k b :=
  (fun s ↦ ⟨orderedPrime z.1.1 z.2 s,
    orderedPrime_mem_block z.1.1 z.2 s⟩,
   orderedBits z.1 z.2)

/-- Product of the primes carrying one specified bit.  Unlike `bitSubset`,
this product retains repeated coordinates in arbitrary target arrays. -/
def slotBitProduct {M k : ℕ} {b : ℕ → ℕ}
    (z : SlotConfiguration M k b) (first : Bool) : ℕ :=
  ∏ s ∈ Finset.univ.filter
      (fun s ↦ if first then (z.2 s).1 else (z.2 s).2), z.1 s

/-- Reciprocal product weight of a slot array. -/
noncomputable def slotConfigurationWeight {M k : ℕ} {b : ℕ → ℕ}
    (z : SlotConfiguration M k b) : ℝ :=
  ∏ s, 1 / ((z.1 s).1 : ℝ)

/-- The two slot products are within a factor two on the logarithmic scale. -/
def SlotClose {M k : ℕ} {b : ℕ → ℕ}
    (z : SlotConfiguration M k b) : Prop :=
  |Real.log (slotBitProduct z true : ℝ) -
    Real.log (slotBitProduct z false : ℝ)| ≤ Real.log 2

theorem slotBitProduct_boundedOrdered_first {M k : ℕ} {b : ℕ → ℕ}
    (x : CloseBlockChoice M k b) (σ : BlockPermutations k b) :
    slotBitProduct (boundedOrderedConfiguration (x, σ)) true = x.2.1.1.prod id := by
  change (∏ s ∈ Finset.univ.filter
      (fun s ↦ (orderedBits x σ s).1), orderedPrime x.1 σ s) = _
  let A := Finset.univ.filter (fun s ↦ (orderedBits x σ s).1)
  have himage := Finset.prod_image
    (s := A) (g := orderedPrime x.1 σ) (f := id)
    (orderedPrime_injective x.1 σ).injOn
  calc
    (∏ s ∈ A, orderedPrime x.1 σ s) =
        ∏ p ∈ A.image (orderedPrime x.1 σ), p := by
      simpa only [id_eq] using himage.symm
    _ = ∏ p ∈ bitSubset (orderedPrime x.1 σ) (orderedBits x σ) true, p := by
      rfl
    _ = x.2.1.1.prod id := by
      rw [bitSubset_orderedBits_first]
      rfl

theorem slotBitProduct_boundedOrdered_second {M k : ℕ} {b : ℕ → ℕ}
    (x : CloseBlockChoice M k b) (σ : BlockPermutations k b) :
    slotBitProduct (boundedOrderedConfiguration (x, σ)) false = x.2.1.2.prod id := by
  change (∏ s ∈ Finset.univ.filter
      (fun s ↦ (orderedBits x σ s).2), orderedPrime x.1 σ s) = _
  let A := Finset.univ.filter (fun s ↦ (orderedBits x σ s).2)
  have himage := Finset.prod_image
    (s := A) (g := orderedPrime x.1 σ) (f := id)
    (orderedPrime_injective x.1 σ).injOn
  calc
    (∏ s ∈ A, orderedPrime x.1 σ s) =
        ∏ p ∈ A.image (orderedPrime x.1 σ), p := by
      simpa only [id_eq] using himage.symm
    _ = ∏ p ∈ bitSubset (orderedPrime x.1 σ) (orderedBits x σ) false, p := by
      rfl
    _ = x.2.1.2.prod id := by
      rw [bitSubset_orderedBits_second]
      rfl

theorem boundedOrderedConfiguration_close {M k : ℕ} {b : ℕ → ℕ}
    (x : CloseBlockChoice M k b) (σ : BlockPermutations k b) :
    SlotClose (boundedOrderedConfiguration (x, σ)) := by
  rw [SlotClose, slotBitProduct_boundedOrdered_first,
    slotBitProduct_boundedOrdered_second]
  exact (mem_subsetClosePairs.mp x.2.2).2.2

theorem boundedOrderedConfiguration_weight {M k : ℕ} {b : ℕ → ℕ}
    (x : CloseBlockChoice M k b) (σ : BlockPermutations k b) :
    slotConfigurationWeight (boundedOrderedConfiguration (x, σ)) =
      selectionWeight (choiceUnion x.1.1) := by
  change (∏ s, 1 / (orderedPrime x.1 σ s : ℝ)) = _
  exact prod_orderedPrime x.1 σ

theorem boundedOrderedConfiguration_injective {M k : ℕ} {b : ℕ → ℕ} :
    Function.Injective
      (boundedOrderedConfiguration (M := M) (k := k) (b := b)) := by
  intro x y hxy
  apply orderedConfiguration_injective
  apply Prod.ext
  · funext s
    exact congrArg (fun z ↦ (z.1 s).1) hxy
  · exact congrArg (fun z ↦ z.2) hxy

/-- All finite close configurations of the prescribed block shape. -/
noncomputable def closeSlotConfigurations (M k : ℕ) (b : ℕ → ℕ) :
    Finset (SlotConfiguration M k b) := by
  classical
  exact Finset.univ.filter SlotClose

theorem boundedOrderedConfiguration_mem {M k : ℕ} {b : ℕ → ℕ}
    (x : CloseBlockChoice M k b) (σ : BlockPermutations k b) :
    boundedOrderedConfiguration (x, σ) ∈ closeSlotConfigurations M k b := by
  classical
  simp [closeSlotConfigurations, boundedOrderedConfiguration_close]

theorem card_blockPermutations (k : ℕ) (b : ℕ → ℕ) :
    Fintype.card (BlockPermutations k b) =
      ∏ i : Fin k, (b i).factorial := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i hi
  simp [Fintype.card_perm]

theorem sum_closeBlockChoice_weight (M k : ℕ) (b : ℕ → ℕ) :
    (∑ x : CloseBlockChoice M k b,
        selectionWeight (choiceUnion x.1.1)) =
      ∑ T ∈ blockChoiceTuples M k b,
        selectionWeight (choiceUnion T) *
          ((subsetClosePairs (choiceUnion T)).card : ℝ) := by
  rw [Fintype.sum_sigma]
  calc
    (∑ T : ↥(blockChoiceTuples M k b),
        ∑ DE : ↥(subsetClosePairs (choiceUnion T.1)),
          selectionWeight (choiceUnion T.1)) =
        ∑ T : ↥(blockChoiceTuples M k b),
          selectionWeight (choiceUnion T.1) *
            ((subsetClosePairs (choiceUnion T.1)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro T hT
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe]
      ring
    _ = _ := by
      rw [← Finset.sum_subtype (blockChoiceTuples M k b)
        (fun T ↦ by simp)
        (fun T ↦ selectionWeight (choiceUnion T) *
          ((subsetClosePairs (choiceUnion T)).card : ℝ))]

theorem sum_orderedSource_weight (M k : ℕ) (b : ℕ → ℕ) :
    (∑ z : CloseBlockChoice M k b × BlockPermutations k b,
        selectionWeight (choiceUnion z.1.1.1)) =
      (∏ i : Fin k, ((b i).factorial : ℝ)) *
        ∑ T ∈ blockChoiceTuples M k b,
          selectionWeight (choiceUnion T) *
            ((subsetClosePairs (choiceUnion T)).card : ℝ) := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [card_blockPermutations]
  push_cast
  rw [← Finset.mul_sum]
  rw [sum_closeBlockChoice_weight]

/-- Ordering the selected primes in every block embeds the weighted sum over
all close divisor-subset pairs into the larger sum over arbitrary close slot
arrays.  Repeated primes are permitted only on the right, which is exactly
the harmless relaxation used in the upper estimate. -/
theorem blockFactorial_mul_closeChoiceWeight_le_slotSum
    (M k : ℕ) (b : ℕ → ℕ) :
    (∏ i : Fin k, ((b i).factorial : ℝ)) *
        (∑ T ∈ blockChoiceTuples M k b,
          selectionWeight (choiceUnion T) *
            ((subsetClosePairs (choiceUnion T)).card : ℝ)) ≤
      ∑ z ∈ closeSlotConfigurations M k b,
        slotConfigurationWeight z := by
  classical
  let E := boundedOrderedConfiguration
    (M := M) (k := k) (b := b)
  have hE : Function.Injective E := boundedOrderedConfiguration_injective
  have himage : Finset.image E Finset.univ ⊆
      closeSlotConfigurations M k b := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact boundedOrderedConfiguration_mem x.1 x.2
  have hnonneg : ∀ z ∈ closeSlotConfigurations M k b,
      z ∉ Finset.image E Finset.univ → 0 ≤ slotConfigurationWeight z := by
    intro z hz hnot
    exact Finset.prod_nonneg fun s hs ↦ by positivity
  calc
    (∏ i : Fin k, ((b i).factorial : ℝ)) *
        (∑ T ∈ blockChoiceTuples M k b,
          selectionWeight (choiceUnion T) *
            ((subsetClosePairs (choiceUnion T)).card : ℝ)) =
        ∑ x : CloseBlockChoice M k b × BlockPermutations k b,
          selectionWeight (choiceUnion x.1.1.1) :=
      (sum_orderedSource_weight M k b).symm
    _ = ∑ z ∈ Finset.image E Finset.univ,
        slotConfigurationWeight z := by
      rw [Finset.sum_image hE.injOn]
      apply Finset.sum_congr rfl
      intro x hx
      exact (boundedOrderedConfiguration_weight x.1 x.2).symm
    _ ≤ ∑ z ∈ closeSlotConfigurations M k b,
        slotConfigurationWeight z :=
      Finset.sum_le_sum_of_subset_of_nonneg himage hnonneg

end Erdos446
