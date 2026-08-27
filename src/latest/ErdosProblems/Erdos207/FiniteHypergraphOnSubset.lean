/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteHypergraphEmbedding

/-! # The exact auxiliary vertex type for a supported hypergraph -/

namespace Erdos207

open Finset

noncomputable section

def finiteHypergraphOnSubset
    {V : Type*} [DecidableEq V] (A : Finset V) (L : Finset (Finset V)) :
    Finset (Finset {v // v ∈ A}) :=
  L.image (fun E ↦ E.subtype (fun v ↦ v ∈ A))

theorem finiteHypergraphOnSubset_decode
    {V : Type*} [DecidableEq V] (A : Finset V) (L : Finset (Finset V))
    (hsupport : ∀ E ∈ L, E ⊆ A) :
    (finiteHypergraphOnSubset A L).image (Finset.map (Function.Embedding.subtype (fun v ↦ v ∈ A))) = L := by
  ext E
  constructor
  · intro hE
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hE
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
    simpa only [subtype_map_of_mem (hsupport D hD)] using hD
  · intro hE
    exact mem_image.mpr ⟨E.subtype (fun v ↦ v ∈ A), mem_image_of_mem _ hE,
      subtype_map_of_mem (hsupport E hE)⟩

theorem mem_finiteHypergraphOnSubset_iff
    {V : Type*} [DecidableEq V] (A : Finset V) (L : Finset (Finset V))
    (hsupport : ∀ E ∈ L, E ⊆ A) (E : Finset {v // v ∈ A}) :
    E ∈ finiteHypergraphOnSubset A L ↔ E.map (Function.Embedding.subtype (fun v ↦ v ∈ A)) ∈ L := by
  constructor
  · intro h
    have hm := mem_image_of_mem (Finset.map (Function.Embedding.subtype (fun v ↦ v ∈ A))) h
    simpa only [finiteHypergraphOnSubset_decode A L hsupport] using hm
  · intro h
    rw [← finiteHypergraphOnSubset_decode A L hsupport] at h
    obtain ⟨D, hD, heq⟩ := mem_image.mp h
    exact (map_injective _ heq) ▸ hD

theorem finiteHypergraphOnSubset_degree
    {V : Type*} [DecidableEq V] (A : Finset V) (L : Finset (Finset V))
    (hsupport : ∀ E ∈ L, E ⊆ A) (v : {v // v ∈ A}) :
    finiteHypergraphDegree (finiteHypergraphOnSubset A L) v = finiteHypergraphDegree L v.val := by
  rw [← finiteHypergraphDegree_image_map (Function.Embedding.subtype (fun v ↦ v ∈ A)),
    finiteHypergraphOnSubset_decode A L hsupport]
  rfl

theorem finiteHypergraphOnSubset_maxDegree
    {V : Type*} [Fintype V] [DecidableEq V] (A : Finset V) (L : Finset (Finset V))
    (hsupport : ∀ E ∈ L, E ⊆ A) :
    finiteHypergraphMaxDegree (finiteHypergraphOnSubset A L) = finiteHypergraphMaxDegree L := by
  rw [← finiteHypergraphMaxDegree_image_map (Function.Embedding.subtype (fun v ↦ v ∈ A)),
    finiteHypergraphOnSubset_decode A L hsupport]

theorem finiteHypergraphOnSubset_uniform
    {V : Type*} [DecidableEq V] (A : Finset V) (L : Finset (Finset V))
    (hsupport : ∀ E ∈ L, E ⊆ A) (k : ℕ) :
    (∀ E ∈ finiteHypergraphOnSubset A L, E.card = k) ↔ ∀ E ∈ L, E.card = k := by
  rw [← finiteHypergraph_image_map_uniform (Function.Embedding.subtype (fun v ↦ v ∈ A)),
    finiteHypergraphOnSubset_decode A L hsupport]

theorem finiteHypergraphOnSubset_union
    {V : Type*} [DecidableEq V] (A : Finset V) (L M : Finset (Finset V)) :
    finiteHypergraphOnSubset A (L ∪ M) = finiteHypergraphOnSubset A L ∪ finiteHypergraphOnSubset A M := by
  exact image_union _ _

theorem univ_map_subset_embedding
    {V : Type*} [DecidableEq V] (A : Finset V) :
    (univ : Finset {v // v ∈ A}).map (Function.Embedding.subtype (fun v ↦ v ∈ A)) = A := by
  ext v
  simp

end

end Erdos207
