/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SphereExpansion

/-! # Exact vertex-embedding transport of forbidden families and greedy states -/

namespace Erdos207

open Finset

noncomputable section

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def mapTripleSystemEmbedding (f : V ↪ W) : TripleSystemOn V ↪ TripleSystemOn W :=
  (Finset.mapEmbedding (mapTripleEmbedding f)).toEmbedding

def mapForbiddenFamily (f : V ↪ W) (F : ForbiddenFamilyOn V) : ForbiddenFamilyOn W :=
  F.map (mapTripleSystemEmbedding f)

@[simp] theorem mapTripleSystem_subset_iff (f : V ↪ W) (C B : TripleSystemOn V) :
    mapTripleSystem f C ⊆ mapTripleSystem f B ↔ C ⊆ B :=
  Finset.map_subset_map

@[simp] theorem mapTripleSystem_insert (f : V ↪ W) (T : TripleOn V) (C : TripleSystemOn V) :
    mapTripleSystem f (insert T C) = insert (mapTriple f T) (mapTripleSystem f C) := by
  exact Finset.map_insert (mapTripleEmbedding f) T C

@[simp] theorem mapTripleSystem_erase (f : V ↪ W) (T : TripleOn V) (C : TripleSystemOn V) :
    mapTripleSystem f (C.erase T) = (mapTripleSystem f C).erase (mapTriple f T) := by
  exact Finset.map_erase (mapTripleEmbedding f) C T

@[simp] theorem mem_mapForbiddenFamily_iff (f : V ↪ W) (F : ForbiddenFamilyOn V) (C : TripleSystemOn V) :
    mapTripleSystem f C ∈ mapForbiddenFamily f F ↔ C ∈ F := by
  exact Finset.mem_map' (mapTripleSystemEmbedding f)

@[simp] theorem isPackingOn_map_iff (f : V ↪ W) (C : TripleSystemOn V) :
    IsPackingOn (mapTripleSystem f C) ↔ IsPackingOn C :=
  ⟨IsPackingOn.of_map, fun h ↦ h.map f⟩

@[simp] theorem avoidsForbidden_map_iff (f : V ↪ W) (C : TripleSystemOn V) (F : ForbiddenFamilyOn V) :
    AvoidsForbidden (mapTripleSystem f C) (mapForbiddenFamily f F) ↔ AvoidsForbidden C F := by
  constructor
  · intro h B hB hBC
    exact h (mapTripleSystem f B) ((mem_mapForbiddenFamily_iff f F B).2 hB)
      ((mapTripleSystem_subset_iff f B C).2 hBC)
  · intro h B hB hBC
    obtain ⟨B', hB', rfl⟩ := mem_map.mp hB
    exact h B' hB' ((mapTripleSystem_subset_iff f B' C).1 hBC)

@[simp] theorem isLegalExtension_map_iff (f : V ↪ W) (F : ForbiddenFamilyOn V)
    (C : TripleSystemOn V) (T : TripleOn V) :
    IsLegalExtension (mapForbiddenFamily f F) (mapTripleSystem f C) (mapTriple f T) ↔
      IsLegalExtension F C T := by
  simp only [IsLegalExtension, ← mapTripleSystem_insert, mem_mapTripleSystem_iff,
    isPackingOn_map_iff, avoidsForbidden_map_iff]

def mapGreedyState (f : V ↪ W) (S : GreedyStateOn V) : GreedyStateOn W where
  chosen := mapTripleSystem f S.chosen
  available := mapTripleSystem f S.available

theorem mapGreedyState_injective (f : V ↪ W) : Function.Injective (mapGreedyState f) := by
  intro S R h
  have hc := (mapTripleSystemEmbedding f).injective (congrArg GreedyStateOn.chosen h)
  have ha := (mapTripleSystemEmbedding f).injective (congrArg GreedyStateOn.available h)
  cases S
  cases R
  simp_all

@[simp] theorem greedyInvariant_map_iff (f : V ↪ W) (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) :
    GreedyInvariant (mapForbiddenFamily f F) (mapGreedyState f S) ↔ GreedyInvariant F S := by
  constructor
  · intro h
    exact ⟨(isPackingOn_map_iff f S.chosen).1 h.1, (avoidsForbidden_map_iff f S.chosen F).1 h.2.1,
      fun T hT ↦ (isLegalExtension_map_iff f F S.chosen T).1
        (h.2.2 (mapTriple f T) ((mem_mapTripleSystem_iff f S.available T).2 hT))⟩
  · intro h
    refine ⟨(isPackingOn_map_iff f S.chosen).2 h.1, (avoidsForbidden_map_iff f S.chosen F).2 h.2.1, ?_⟩
    intro T hT
    obtain ⟨T', hT', rfl⟩ := mem_map.mp hT
    exact (isLegalExtension_map_iff f F S.chosen T').2 (h.2.2 T' hT')

theorem legalAvailable_map [Fintype V] [Fintype W] (f : V ↪ W) (F : ForbiddenFamilyOn V)
    (C A : TripleSystemOn V) :
    mapTripleSystem f (legalAvailable F C A) =
      legalAvailable (mapForbiddenFamily f F) (mapTripleSystem f C) (mapTripleSystem f A) := by
  classical
  change (A.filter (IsLegalExtension F C)).map (mapTripleEmbedding f) =
    (A.map (mapTripleEmbedding f)).filter (IsLegalExtension (mapForbiddenFamily f F) (mapTripleSystem f C))
  rw [filter_map]
  apply congrArg (fun B : TripleSystemOn V ↦ B.map (mapTripleEmbedding f))
  apply filter_congr
  intro T _
  exact (isLegalExtension_map_iff f F C T).symm

theorem greedyStep_map [Fintype V] [Fintype W] (f : V ↪ W) (F : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (T : TripleOn V) :
    mapGreedyState f (greedyStep F S T) =
      greedyStep (mapForbiddenFamily f F) (mapGreedyState f S) (mapTriple f T) := by
  apply congrArg₂ GreedyStateOn.mk
  · exact mapTripleSystem_insert f T S.chosen
  · change mapTripleSystem f (legalAvailable F (insert T S.chosen) (S.available.erase T)) = _
    rw [legalAvailable_map, mapTripleSystem_insert, mapTripleSystem_erase]
    rfl

end

end Erdos207
