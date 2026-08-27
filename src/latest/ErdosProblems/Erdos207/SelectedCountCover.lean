/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SelectedWitnessImage
import ErdosProblems.Erdos207.DependentSigmaExtension

/-! # Decoded covers and dependent sums of selected witnesses -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem selectedCount_eq_card_filter
    {I W : Type*} [Fintype I] [DecidableEq W]
    (rem : I → Finset W) (R : Finset W) :
    selectedCount rem R = ((univ.filter fun i ↦ rem i ⊆ R).card : ℝ≥0) := by
  classical
  unfold selectedCount
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem selectedCount_le_of_decoded_cover
    {I J W Y : Type*} [Fintype I] [Fintype J] [DecidableEq W] [DecidableEq Y]
    (remI : I → Finset W) (remJ : J → Finset W) (f : I → Y) (g : J → Y)
    (R S : Finset W) (hf : Function.Injective f)
    (hcover : ∀ i, remI i ⊆ R → ∃ j, remJ j ⊆ S ∧ g j = f i) :
    selectedCount remI R ≤ selectedCount remJ S := by
  classical
  rw [selectedCount_eq_card_filter]
  have hc : (univ.filter fun i ↦ remI i ⊆ R).card ≤ (selectedWitnessImage remJ g S).card := by
    apply card_le_card_of_injOn f
    · intro i hi
      exact mem_selectedWitnessImage.mpr (hcover i (mem_filter.mp hi).2)
    · exact fun _ _ _ _ h ↦ hf h
  have hc' : ((univ.filter fun i ↦ remI i ⊆ R).card : ℝ≥0) ≤
      ((selectedWitnessImage remJ g S).card : ℝ≥0) := by exact_mod_cast hc
  exact hc'.trans (card_selectedWitnessImage_le_selectedCount remJ g S)

theorem selectedCount_sigma
    {W E : Type*} [DecidableEq W] [Fintype E]
    {I : E → Type*} [∀ e, Fintype (I e)]
    (F : ∀ e, I e → Finset W) (R : Finset W) :
    selectedCount (fun z : Σ e, I e ↦ F z.1 z.2) R = ∑ e, selectedCount (F e) R := by
  unfold selectedCount
  rw [Fintype.sum_sigma]

theorem hasExtensionBound_sigma_sum
    {W E : Type*} [DecidableEq W] [Fintype E]
    {I : E → Type*} [∀ e, Fintype (I e)]
    (F : ∀ e, I e → Finset W) (pi : W → ℝ≥0) (kappa : E → ℝ≥0)
    (hF : ∀ e, HasExtensionBound (F e) pi (kappa e)) :
    HasExtensionBound (fun z : Σ e, I e ↦ F z.1 z.2) pi (∑ e, kappa e) := by
  intro H
  unfold extensionWeight
  change (∑ z : Σ e, I e, if H ⊆ F z.1 z.2 then setWeight pi (F z.1 z.2 \ H) else 0) ≤ _
  rw [Fintype.sum_sigma]
  exact sum_le_sum fun e _ ↦ hF e H

end

end Erdos207
