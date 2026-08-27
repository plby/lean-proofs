/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedTwoAwayStateBounds
import ErdosProblems.Erdos207.GlobalPatternJump
import ErdosProblems.Erdos207.DyadicCrudeCutoffs

/-! # In the sparse-stage size regime, pair-crude bounds supply localized pattern cutoffs -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem CrudeStateBounds.allLocalized
    {I V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (F : ForbiddenFamilyOn V) (hpack : ∀ E ∈ F, IsPackingOn E)
    (sets : I → Finset V) (cutoff : I → ℝ≥0) (S : GreedyStateOn V) (K : CrudeThresholds)
    (h : CrudeStateBounds F S q K) (hK : ∀ i, K.pair ≤ cutoff i) :
    AllLocalizedTwoAwayBounds F sets cutoff S := by
  intro i T a b hab
  have hp := h (.inr (.inl (T, ⟨{a, b}, card_pair hab⟩)))
  exact ((localizedTwoAway_selectedCount_le_pair F T (sets i) S.chosen hpack hab).trans_lt hp).trans_le (hK i)

theorem CrudeStateBounds.allLocalized_power
    {I V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (F : ForbiddenFamilyOn V) (hpack : ∀ E ∈ F, IsPackingOn E)
    (sets : I → Finset V) (S : GreedyStateOn V) (t k r : ℕ) (ht : 1 ≤ t)
    (h : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (hsize : ∀ i, t ^ (k + r) ≤ (sets i).card) :
    AllLocalizedTwoAwayBounds F sets (fun i ↦ ((sets i).card : ℝ≥0) / (t : ℝ≥0) ^ r) S := by
  apply CrudeStateBounds.allLocalized F hpack sets _ S _ h
  intro i
  have ht0 : (0 : ℝ≥0) < t := by exact_mod_cast (show 0 < t by omega)
  apply (le_div_iff₀ (pow_pos ht0 r)).2
  change (t : ℝ≥0) ^ k * (t : ℝ≥0) ^ r ≤ (sets i).card
  rw [← pow_add]
  exact_mod_cast hsize i

end

end Erdos207
