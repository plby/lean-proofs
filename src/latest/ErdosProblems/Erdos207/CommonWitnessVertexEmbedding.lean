/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyClassVertexEmbedding
import ErdosProblems.Erdos207.SelectedWitnessEmbedding

/-! # Distinct common witnesses and their selected remainders survive vertex maps -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def CommonThreatWitness.mapVertices (f : V ↪ W) {F G : ForbiddenFamilyOn V} {T T' : TripleOn V}
    (u : CommonThreatWitness F G T T') :
    CommonThreatWitness (mapForbiddenFamily f F) (mapForbiddenFamily f G) (mapTriple f T) (mapTriple f T') where
  bridge := mapTriple f u.bridge
  first := mapTripleSystem f u.first
  second := mapTripleSystem f u.second
  first_mem := (mem_mapForbiddenFamily_iff f F u.first).2 u.first_mem
  second_mem := (mem_mapForbiddenFamily_iff f G u.second).2 u.second_mem
  first_root := (mem_mapTripleSystem_iff f u.first T).2 u.first_root
  second_root := (mem_mapTripleSystem_iff f u.second T').2 u.second_root
  bridge_first := (mem_mapTripleSystem_iff f u.first u.bridge).2 u.bridge_first
  bridge_second := (mem_mapTripleSystem_iff f u.second u.bridge).2 u.bridge_second
  bridge_ne_first := (mapTriple_injective f).ne u.bridge_ne_first
  bridge_ne_second := (mapTriple_injective f).ne u.bridge_ne_second
  first_cross h := congrArg (mapTriple f) (u.first_cross ((mem_mapTripleSystem_iff f u.first T').1 h))
  second_cross h := congrArg (mapTriple f) (u.second_cross ((mem_mapTripleSystem_iff f u.second T).1 h))
  different := (mapTripleSystemEmbedding f).injective.ne u.different

theorem CommonThreatWitness.mapVertices_injective (f : V ↪ W)
    (F G : ForbiddenFamilyOn V) (T T' : TripleOn V) :
    Function.Injective (CommonThreatWitness.mapVertices f : CommonThreatWitness F G T T' → _) := by
  intro u v h
  have hb := (mapTriple_injective f) (congrArg CommonThreatWitness.bridge h)
  have hf := (mapTripleSystemEmbedding f).injective (congrArg CommonThreatWitness.first h)
  have hs := (mapTripleSystemEmbedding f).injective (congrArg CommonThreatWitness.second h)
  change u.bridge = v.bridge at hb
  change u.first = v.first at hf
  change u.second = v.second at hs
  cases u
  cases v
  simp_all

theorem CommonThreatWitness.mapVertices_remainder (f : V ↪ W)
    {F G : ForbiddenFamilyOn V} {T T' : TripleOn V} (u : CommonThreatWitness F G T T') :
    (u.mapVertices f).remainder = mapTripleSystem f u.remainder := by
  simp only [CommonThreatWitness.remainder, CommonThreatWitness.leftRemainder,
    CommonThreatWitness.rightRemainder, CommonThreatWitness.mapVertices,
    mapTripleSystem_union, mapTripleSystem_erase]

theorem commonThreat_selectedCount_le_map [Fintype V] [Fintype W] (f : V ↪ W) (F G : ForbiddenFamilyOn V)
    (T T' : TripleOn V) (R : TripleSystemOn V) :
    selectedCount (fun u : CommonThreatWitness F G T T' ↦ u.remainder) R ≤
      selectedCount (fun u : CommonThreatWitness (mapForbiddenFamily f F) (mapForbiddenFamily f G)
        (mapTriple f T) (mapTriple f T') ↦ u.remainder) (mapTripleSystem f R) :=
  selectedCount_le_of_mapped_injection _ _ (mapTripleEmbedding f) (CommonThreatWitness.mapVertices f)
    (CommonThreatWitness.mapVertices_injective f F G T T') (fun u ↦ u.mapVertices_remainder f) R

end

end Erdos207
