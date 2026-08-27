/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonWitnessVertexEmbedding
import ErdosProblems.Erdos207.PairWitnessVertexEmbedding
import ErdosProblems.Erdos207.MappedStoppedProcess

/-! # Ambient crude bounds imply the exact current-vertex crude bounds -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {q : ℕ}

def mapCrudeStatisticIndex (f : V ↪ W) : CrudeStatisticIndex V q → CrudeStatisticIndex W q
  | .inl (j, roots) => .inl (j, ⟨(mapTriple f roots.1.1, mapTriple f roots.1.2),
      (mapTriple_injective f).ne roots.2⟩)
  | .inr (.inl (T, P)) => .inr (.inl (mapTriple f T, mapPairOn f P))
  | .inr (.inr (.inl (T, T'))) => .inr (.inr (.inl (mapTriple f T, mapTriple f T')))
  | .inr (.inr (.inr (j, T))) => .inr (.inr (.inr (j, mapTriple f T)))

@[simp] theorem crudeThreshold_map_index (f : V ↪ W) (K : CrudeThresholds) (i : CrudeStatisticIndex V q) :
    crudeThreshold K (mapCrudeStatisticIndex f i) = crudeThreshold K i := by
  rcases i with ⟨j, roots⟩ | ⟨T, P⟩ | ⟨T, T'⟩ | ⟨j, T⟩ <;> rfl

variable [Fintype V] [Fintype W]

theorem crudeStatistic_le_map (f : V ↪ W) (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (i : CrudeStatisticIndex V q) :
    crudeStatistic F S i ≤ crudeStatistic (mapForbiddenFamily f F) (mapGreedyState f S) (mapCrudeStatisticIndex f i) := by
  rcases i with ⟨j, roots⟩ | ⟨T, P⟩ | ⟨T, T'⟩ | ⟨j, T⟩
  · change ((greedyRootedConfigurationClass (forbiddenFamilyOfOrder F j.order) S {roots.1.1, roots.1.2} j.chosen).card : ℝ≥0) ≤
      (greedyRootedConfigurationClass (forbiddenFamilyOfOrder (mapForbiddenFamily f F) j.order)
        (mapGreedyState f S) {mapTriple f roots.1.1, mapTriple f roots.1.2} j.chosen).card
    rw [← forbiddenFamilyOfOrder_map, ← mapTripleSystem_pair]
    exact_mod_cast greedyRootedConfigurationClass_card_le_map f (forbiddenFamilyOfOrder F j.order) S {roots.1.1, roots.1.2} j.chosen
  · exact pairThreat_selectedCount_le_map f F T P S.chosen
  · exact commonThreat_selectedCount_le_map f F F T T' S.chosen
  · change (greedyActiveGainDefectCount (forbiddenFamilyOfOrder F j.order) F S T j.chosen : ℝ≥0) ≤
      greedyActiveGainDefectCount (forbiddenFamilyOfOrder (mapForbiddenFamily f F) j.order)
        (mapForbiddenFamily f F) (mapGreedyState f S) (mapTriple f T) j.chosen
    rw [← forbiddenFamilyOfOrder_map]
    exact_mod_cast greedyActiveGainDefectCount_le_map f (forbiddenFamilyOfOrder F j.order) F S T j.chosen

theorem CrudeStateBounds.of_map (f : V ↪ W) (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (K : CrudeThresholds) (h : CrudeStateBounds (mapForbiddenFamily f F) (mapGreedyState f S) q K) :
    CrudeStateBounds F S q K := by
  intro i
  exact (crudeStatistic_le_map f F S i).trans_lt (by simpa only [crudeThreshold_map_index] using h (mapCrudeStatisticIndex f i))

theorem probability_crude_failure_le_mapped_timed_law (f : V ↪ W) (n : ℕ) (F : ForbiddenFamilyOn V)
    (L : FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) n)) (K : CrudeThresholds) :
    L.probability (fun u ↦ ¬ CrudeStateBounds F u.2 q K) ≤
      (FiniteLaw.map (fun u : FiniteLaw.TimedState (GreedyStateOn V) n ↦ (u.1, mapGreedyState f u.2)) L).probability
        (fun u ↦ ¬ CrudeStateBounds (mapForbiddenFamily f F) u.2 q K) := by
  rw [FiniteLaw.probability_map]
  apply L.probability_mono
  intro u hu hmap
  exact hu (CrudeStateBounds.of_map f F u.2 K hmap)

end

end Erdos207
