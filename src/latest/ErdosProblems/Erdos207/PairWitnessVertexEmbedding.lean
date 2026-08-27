/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyClassVertexEmbedding
import ErdosProblems.Erdos207.SelectedWitnessEmbedding

/-! # Pair-local threat witnesses preserve their pinned pair and exact remainder -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def mapPairOn (f : V ↪ W) (P : PairOn V) : PairOn W :=
  ⟨P.1.map f, by rw [card_map]; exact P.2⟩

variable [Fintype V] [Fintype W]

theorem mem_triplesSharingPair_map_iff (f : V ↪ W) (T U : TripleOn V) :
    mapTriple f U ∈ triplesSharingPair (mapTriple f T) ↔ U ∈ triplesSharingPair T := by
  simp only [mem_triplesSharingPair_iff, mapTriple, ← Finset.map_inter, card_map]

def mapPairThreatWitness (f : V ↪ W) {F : ForbiddenFamilyOn V} {T : TripleOn V} {P : PairOn V}
    (u : PairTwoAwayThreatWitness V F T P) :
    PairTwoAwayThreatWitness W (mapForbiddenFamily f F) (mapTriple f T) (mapPairOn f P) := by
  refine ⟨⟨(mapTripleSystem f u.1.1.1, mapTriple f u.1.1.2),
    (mem_mapForbiddenFamily_iff f F u.1.1.1).2 u.1.2.1,
    (mem_mapTripleSystem_iff f u.1.1.1 u.1.1.2).2 u.1.2.2.1,
    (mem_mapTripleSystem_iff f u.1.1.1 T).2 u.1.2.2.2.1,
    (mapTriple_injective f).ne u.1.2.2.2.2⟩, ?_, ?_⟩
  · exact Finset.map_subset_map.mpr u.2.1
  · exact fun h ↦ u.2.2 ((mem_triplesSharingPair_map_iff f T u.1.1.2).1 h)

theorem mapPairThreatWitness_injective (f : V ↪ W) (F : ForbiddenFamilyOn V) (T : TripleOn V) (P : PairOn V) :
    Function.Injective (mapPairThreatWitness f : PairTwoAwayThreatWitness V F T P → _) := by
  intro u v h
  have hE := (mapTripleSystemEmbedding f).injective (congrArg (fun z ↦ z.1.1.1) h)
  have hU := (mapTriple_injective f) (congrArg (fun z ↦ z.1.1.2) h)
  change u.1.1.1 = v.1.1.1 at hE
  change u.1.1.2 = v.1.1.2 at hU
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hE hU

theorem mapPairThreatWitness_remainder (f : V ↪ W)
    {F : ForbiddenFamilyOn V} {T : TripleOn V} {P : PairOn V} (u : PairTwoAwayThreatWitness V F T P) :
    pairTwoAwayThreatRemainder (mapPairThreatWitness f u) = mapTripleSystem f (pairTwoAwayThreatRemainder u) := by
  simp only [pairTwoAwayThreatRemainder, twoAwayThreatRemainder, mapPairThreatWitness, mapTripleSystem_erase]

theorem pairThreat_selectedCount_le_map (f : V ↪ W) (F : ForbiddenFamilyOn V)
    (T : TripleOn V) (P : PairOn V) (R : TripleSystemOn V) :
    selectedCount (fun u : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder u) R ≤
      selectedCount (fun u : PairTwoAwayThreatWitness W (mapForbiddenFamily f F)
        (mapTriple f T) (mapPairOn f P) ↦ pairTwoAwayThreatRemainder u) (mapTripleSystem f R) :=
  selectedCount_le_of_mapped_injection _ _ (mapTripleEmbedding f) (mapPairThreatWitness f)
    (mapPairThreatWitness_injective f F T P) (fun u ↦ mapPairThreatWitness_remainder f u) R

end

end Erdos207
