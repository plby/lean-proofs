/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightSystem

/-! # Images of selected configuration witnesses -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def selectedWitnessImage
    {I W Y : Type*} [Fintype I] [DecidableEq W] [DecidableEq Y]
    (rem : I → Finset W) (f : I → Y) (R : Finset W) : Finset Y := by
  classical
  exact (univ.filter fun u ↦ rem u ⊆ R).image f

theorem mem_selectedWitnessImage
    {I W Y : Type*} [Fintype I] [DecidableEq W] [DecidableEq Y]
    {rem : I → Finset W} {f : I → Y} {R : Finset W} {y : Y} :
    y ∈ selectedWitnessImage rem f R ↔ ∃ u, rem u ⊆ R ∧ f u = y := by
  classical
  simp [selectedWitnessImage]

theorem card_selectedWitnessImage_le_selectedCount
    {I W Y : Type*} [Fintype I] [DecidableEq W] [DecidableEq Y]
    (rem : I → Finset W) (f : I → Y) (R : Finset W) :
    ((selectedWitnessImage rem f R).card : ℝ≥0) ≤ selectedCount rem R := by
  classical
  have hc : ((univ.filter fun u ↦ rem u ⊆ R).card : ℝ≥0) = selectedCount rem R := by
    unfold selectedCount
    simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← hc]
  exact_mod_cast (card_image_le (s := univ.filter fun u ↦ rem u ⊆ R) (f := f))

end

end Erdos207
