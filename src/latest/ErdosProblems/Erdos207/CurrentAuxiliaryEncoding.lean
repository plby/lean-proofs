/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CurrentVertexGraphEncoding
import ErdosProblems.Erdos207.LocalForbiddenStoppedLaw
import ErdosProblems.Erdos207.RegularizedKSSSPowerParameters

/-! # Keep the actual auxiliary triangle indices while changing the vertex universe -/

namespace Erdos207

open Finset

noncomputable section

def restrictTripleIndexEmbedding
    {V I : Type*} [Fintype V] [DecidableEq V]
    (D : Finset V) (e : I ↪ TripleOn V) (hsupport : ∀ i, (e i).1 ⊆ D) : I ↪ TripleOn D where
  toFun i := restrictSupportedTriple D ⟨e i, mem_triplesSupportedOn_iff.mpr (hsupport i)⟩
  inj' := by
    intro i j hij
    apply e.injective
    have h := congrArg (mapTriple (Function.Embedding.subtype (fun v ↦ v ∈ D))) hij
    simpa only [map_restrictSupportedTriple] using h

theorem map_restrictTripleIndexEmbedding
    {V I : Type*} [Fintype V] [DecidableEq V]
    (D : Finset V) (e : I ↪ TripleOn V) (hsupport : ∀ i, (e i).1 ⊆ D) (i : I) :
    mapTriple (Function.Embedding.subtype (fun v ↦ v ∈ D)) (restrictTripleIndexEmbedding D e hsupport i) =
      e i :=
  map_restrictSupportedTriple D _

theorem map_family_restrictTripleIndexEmbedding
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (D : Finset V) (e : I ↪ TripleOn V) (hsupport : ∀ i, (e i).1 ⊆ D) (C : Finset I) :
    mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ D))
      (C.map (restrictTripleIndexEmbedding D e hsupport)) = C.map e := by
  unfold mapTripleSystem
  rw [map_map]
  congr 1
  apply Function.Embedding.ext
  intro i
  exact map_restrictTripleIndexEmbedding D e hsupport i

theorem restrictTripleIndexEmbedding_univ
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (D : Finset V) (e : I ↪ TripleOn V) (A : TripleSystemOn V)
    (hencode : univ.map e = A) (hsupport : ∀ i, (e i).1 ⊆ D) :
    univ.map (restrictTripleIndexEmbedding D e hsupport) = restrictTripleSystemTo D A := by
  apply (Finset.map_injective (mapTripleEmbedding (Function.Embedding.subtype (fun v ↦ v ∈ D))))
  change mapTripleSystem _ _ = mapTripleSystem _ _
  rw [map_family_restrictTripleIndexEmbedding, hencode, map_restrictTripleSystemTo]
  intro T hT
  rw [← hencode] at hT
  obtain ⟨i, _, rfl⟩ := mem_map.mp hT
  exact hsupport i

theorem restrictTripleIndexEmbedding_packing
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (D : Finset V) (e : I ↪ TripleOn V) (hsupport : ∀ i, (e i).1 ⊆ D) (C : Finset I) :
    IsPackingOn (C.map (restrictTripleIndexEmbedding D e hsupport)) ↔ IsPackingOn (C.map e) := by
  rw [← map_family_restrictTripleIndexEmbedding D e hsupport C, isPackingOn_map_iff]

theorem regularizedForbiddenUnion_restrict_index_map
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (D : Finset V) (e : I ↪ TripleOn V) (hsupport : ∀ i, (e i).1 ⊆ D)
    (q : ℕ) (Lstar : ℕ → Finset (Finset I)) :
    mapForbiddenFamily (Function.Embedding.subtype (fun v ↦ v ∈ D))
      (regularizedForbiddenUnion (restrictTripleIndexEmbedding D e hsupport) q Lstar) =
        regularizedForbiddenUnion e q Lstar := by
  ext H
  simp only [mapForbiddenFamily, regularizedForbiddenUnion, mem_map, mem_image]
  constructor
  · rintro ⟨C, ⟨B, hB, rfl⟩, rfl⟩
    exact ⟨B, hB, (map_family_restrictTripleIndexEmbedding D e hsupport B).symm⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨B.map (restrictTripleIndexEmbedding D e hsupport), ⟨B, hB, rfl⟩,
      map_family_restrictTripleIndexEmbedding D e hsupport B⟩

theorem current_regularized_stopped_global_structure
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : Finset V) (A P : TripleSystemOn V) (F : ForbiddenFamilyOn V) (q n : ℕ)
    (hsupport : ∀ T ∈ A, T.1 ⊆ D)
    (Lstar : ℕ → Finset (Finset {T // T ∈ A}))
    (active : ℕ → GreedyStateOn D → Prop)
    (huniform : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, E.card = j - 2)
    (G : SimpleGraph V) (horder : ∀ C ∈ F, C.card + 2 ≤ q)
    (hP : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hsingle : ∀ T ∈ A, ¬ CompletesForbidden F P T)
    (hgraph : G ≤ leaveGraph P) (htri : ConsistsOfTriangles G A)
    (hcovers : ∀ j ∈ Icc 4 q,
      ∀ E ∈ finiteHypergraphOnSubset A (localForbiddenConfigurations F A P j),
        ∃ C ∈ (Ico 4 j).biUnion Lstar ∪ Lstar j, C ⊆ E) :
    let e := Function.Embedding.subtype (fun T ↦ T ∈ A)
    let f := Function.Embedding.subtype (fun v ↦ v ∈ D)
    let J := regularizedForbiddenUnion (restrictTripleIndexEmbedding D e (fun T ↦ hsupport T.val T.property)) q Lstar
    (stoppedGreedyStateLaw n J active ⟨∅, restrictTripleSystemTo D A⟩).SupportedOn fun S ↦
      let M := mapTripleSystem f S.chosen
      M ⊆ A ∧ IsPackingOn (P ∪ M) ∧ Disjoint P M ∧ AvoidsForbidden (P ∪ M) F := by
  dsimp only
  let e := Function.Embedding.subtype (fun T ↦ T ∈ A)
  let f := Function.Embedding.subtype (fun v ↦ v ∈ D)
  let elocal := restrictTripleIndexEmbedding D e (fun T ↦ hsupport T.val T.property)
  let J := regularizedForbiddenUnion elocal q Lstar
  let S₀ : GreedyStateOn D := ⟨∅, restrictTripleSystemTo D A⟩
  have hInv := regularizedForbiddenUnion_initial_invariant elocal q Lstar huniform S₀.available
  have hsupp := stoppedGreedyStateLaw_supported n J active S₀ hInv rfl
  intro S hmass
  have hS := hsupp S hmass
  have hMA : mapTripleSystem f S.chosen ⊆ A := by
    have hm := mapTripleSystem_mono f hS.2.2
    simpa only [S₀, f, map_restrictTripleSystemTo D A hsupport] using hm
  have havoid := (avoidsForbidden_map_iff f S.chosen J).mpr hS.1.2.1
  rw [regularizedForbiddenUnion_restrict_index_map D e (fun T ↦ hsupport T.val T.property) q Lstar] at havoid
  have hlocal := avoids_original_union_of_regularized e q
    (fun j ↦ finiteHypergraphOnSubset A (localForbiddenConfigurations F A P j)) Lstar hcovers
    (mapTripleSystem f S.chosen) havoid
  rw [regularizedForbiddenUnion_local_decode] at hlocal
  exact ⟨hMA, localNibble_global_structure horder hP hPavoid hsingle hgraph htri hMA
    (hS.1.1.map f) hlocal⟩

end

end Erdos207
