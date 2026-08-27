/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyVertexEmbedding
import ErdosProblems.Erdos207.CrudeStatisticIndex

/-! # Rooted and gain configuration counts under an injective vertex map -/

namespace Erdos207

open Finset

noncomputable section

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

@[simp] theorem mapTripleSystem_union (f : V ↪ W) (C B : TripleSystemOn V) :
    mapTripleSystem f (C ∪ B) = mapTripleSystem f C ∪ mapTripleSystem f B := Finset.map_union C B

@[simp] theorem mapTripleSystem_inter (f : V ↪ W) (C B : TripleSystemOn V) :
    mapTripleSystem f (C ∩ B) = mapTripleSystem f C ∩ mapTripleSystem f B := Finset.map_inter C B

@[simp] theorem mapTripleSystem_sdiff (f : V ↪ W) (C B : TripleSystemOn V) :
    mapTripleSystem f (C \ B) = mapTripleSystem f C \ mapTripleSystem f B := Finset.map_sdiff C B

@[simp] theorem mapTripleSystem_eq_iff (f : V ↪ W) (C B : TripleSystemOn V) :
    mapTripleSystem f C = mapTripleSystem f B ↔ C = B := (mapTripleSystemEmbedding f).injective.eq_iff

@[simp] theorem mapTripleSystem_pair (f : V ↪ W) (T U : TripleOn V) :
    mapTripleSystem f {T, U} = {mapTriple f T, mapTriple f U} := by
  simp [mapTripleSystem, mapTripleEmbedding]

theorem forbiddenFamilyOfOrder_map (f : V ↪ W) (F : ForbiddenFamilyOn V) (j : ℕ) :
    mapForbiddenFamily f (forbiddenFamilyOfOrder F j) = forbiddenFamilyOfOrder (mapForbiddenFamily f F) j := by
  classical
  change (F.filter fun C ↦ C.card = j - 2).map (mapTripleSystemEmbedding f) =
    (F.map (mapTripleSystemEmbedding f)).filter fun C ↦ C.card = j - 2
  rw [filter_map]
  apply congrArg (fun B : ForbiddenFamilyOn V ↦ B.map (mapTripleSystemEmbedding f))
  apply filter_congr
  intro C _
  change (C.card = j - 2) ↔ (mapTripleSystem f C).card = j - 2
  rw [card_mapTripleSystem]

variable [Fintype V] [Fintype W]

theorem mem_greedyRootedConfigurationClass_map_iff (f : V ↪ W) (J : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (R C : TripleSystemOn V) (c : ℕ) :
    mapTripleSystem f C ∈ greedyRootedConfigurationClass (mapForbiddenFamily f J)
      (mapGreedyState f S) (mapTripleSystem f R) c ↔ C ∈ greedyRootedConfigurationClass J S R c := by
  simp only [greedyRootedConfigurationClass, mem_filter, mem_mapForbiddenFamily_iff, mapGreedyState,
    ← mapTripleSystem_inter, ← mapTripleSystem_union, mapTripleSystem_subset_iff, card_mapTripleSystem]

theorem mem_greedyConfigurationClass_map_iff (f : V ↪ W) (J : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (T : TripleOn V) (C : TripleSystemOn V) (c : ℕ) :
    mapTripleSystem f C ∈ greedyConfigurationClass (mapForbiddenFamily f J)
      (mapGreedyState f S) (mapTriple f T) c ↔ C ∈ greedyConfigurationClass J S T c := by
  simp only [mem_greedyConfigurationClass, mem_mapForbiddenFamily_iff, mapGreedyState,
    mem_mapTripleSystem_iff, ← mapTripleSystem_inter, ← mapTripleSystem_union,
    mapTripleSystem_subset_iff, card_mapTripleSystem]

theorem mem_greedyConfigurationRedundantWitnesses_map_iff (f : V ↪ W) (F : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (C B : TripleSystemOn V) :
    mapTripleSystem f B ∈ greedyConfigurationRedundantWitnesses (mapForbiddenFamily f F)
      (mapGreedyState f S) (mapTripleSystem f C) ↔ B ∈ greedyConfigurationRedundantWitnesses F S C := by
  simp only [greedyConfigurationRedundantWitnesses, mem_filter, mem_mapForbiddenFamily_iff,
    mapGreedyState, ne_eq, mapTripleSystem_eq_iff, ← mapTripleSystem_inter, ← mapTripleSystem_sdiff,
    mapTripleSystem_subset_iff, card_mapTripleSystem]

theorem greedyRootedConfigurationClass_card_le_map (f : V ↪ W) (J : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (R : TripleSystemOn V) (c : ℕ) :
    (greedyRootedConfigurationClass J S R c).card ≤
      (greedyRootedConfigurationClass (mapForbiddenFamily f J) (mapGreedyState f S) (mapTripleSystem f R) c).card := by
  apply card_le_card_of_injOn (mapTripleSystem f)
  · intro C hC
    exact (mem_greedyRootedConfigurationClass_map_iff f J S R C c).2 hC
  · exact (mapTripleSystemEmbedding f).injective.injOn

theorem greedyGainDefectPairs_card_le_map (f : V ↪ W) (J G : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (T : TripleOn V) (c : ℕ) :
    (greedyGainDefectPairs J G S T c).card ≤
      (greedyGainDefectPairs (mapForbiddenFamily f J) (mapForbiddenFamily f G)
        (mapGreedyState f S) (mapTriple f T) c).card := by
  classical
  apply card_le_card_of_injOn (fun p : TripleSystemOn V × TripleSystemOn V ↦
    (mapTripleSystem f p.1, mapTripleSystem f p.2))
  · intro p hp
    have hd := mem_filter.mp hp
    apply mem_filter.mpr
    exact ⟨mem_product.mpr ⟨(mem_greedyConfigurationClass_map_iff f J S T p.1 c).2 (mem_product.mp hd.1).1,
      (mem_mapForbiddenFamily_iff f G p.2).2 (mem_product.mp hd.1).2⟩,
      (mem_greedyConfigurationRedundantWitnesses_map_iff f G S p.1 p.2).2 hd.2.1,
      fun h ↦ hd.2.2 ((mapTripleSystem_subset_iff f p.2 p.1).1 h)⟩
  · intro p _ p' _ hp
    exact Prod.ext ((mapTripleSystemEmbedding f).injective (congrArg Prod.fst hp))
      ((mapTripleSystemEmbedding f).injective (congrArg Prod.snd hp))

theorem greedyActiveGainDefectCount_le_map (f : V ↪ W) (J G : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (T : TripleOn V) (c : ℕ) :
    greedyActiveGainDefectCount J G S T c ≤
      greedyActiveGainDefectCount (mapForbiddenFamily f J) (mapForbiddenFamily f G)
        (mapGreedyState f S) (mapTriple f T) c := by
  classical
  unfold greedyActiveGainDefectCount
  simp only [mapGreedyState, mem_mapTripleSystem_iff]
  split_ifs
  · exact greedyGainDefectPairs_card_le_map f J G S T c
  · exact le_rfl

end

end Erdos207
