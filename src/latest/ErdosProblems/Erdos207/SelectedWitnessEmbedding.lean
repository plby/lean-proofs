/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SelectedCountCover

/-! # Injectively mapped witnesses give a one-sided selected-count bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem selectedCount_le_of_mapped_injection
    {I J A B : Type*} [Fintype I] [Fintype J] [DecidableEq A] [DecidableEq B]
    (F : I → Finset A) (G : J → Finset B) (e : A ↪ B) (f : I → J)
    (hf : Function.Injective f) (hrem : ∀ i, G (f i) = (F i).map e) (R : Finset A) :
    selectedCount F R ≤ selectedCount G (R.map e) := by
  classical
  rw [selectedCount_eq_card_filter, selectedCount_eq_card_filter]
  have hc : (univ.filter fun i ↦ F i ⊆ R).card ≤ (univ.filter fun j ↦ G j ⊆ R.map e).card := by
    apply card_le_card_of_injOn f
    · intro i hi
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      rw [hrem, map_subset_map]
      exact (mem_filter.mp hi).2
    · exact hf.injOn
  exact_mod_cast hc

end

end Erdos207
