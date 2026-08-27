/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceTriangleRegularizationTheorem
import ErdosProblems.Erdos207.PreliminaryEdgeSupply

/-! # Exact graph-edge and triangle encodings for the finite regularizer -/

namespace Erdos207

open Finset

noncomputable section

theorem sym2_toFinset_injective {V : Type*} [DecidableEq V] :
    Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
  intro e f heq
  apply Sym2.ext
  intro v
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, heq]

def graphPairFamily {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Finset V) :=
  (graphEdges G).image Sym2.toFinset

def triangleVertexFamily {V : Type*} [DecidableEq V]
    (A : TripleSystemOn V) : Finset (Finset V) := A.image Subtype.val

theorem graphPairFamily_card
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (graphPairFamily G).card = (graphEdges G).card :=
  card_image_of_injective _ sym2_toFinset_injective

theorem graphPairFamily_uniform
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ∀ P ∈ graphPairFamily G, P.card = 2 := by
  intro P hP
  obtain ⟨e, he, rfl⟩ := mem_image.mp hP
  exact Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))

theorem triangleVertexFamily_uniform
    {V : Type*} [DecidableEq V] (A : TripleSystemOn V) :
    ∀ T ∈ triangleVertexFamily A, T.card = 3 := by
  intro T hT
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hT
  exact U.2

theorem mem_graphPairFamily_toFinset_iff
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (e : Sym2 V) :
    e.toFinset ∈ graphPairFamily G ↔ e ∈ graphEdges G := by
  constructor
  · intro h
    obtain ⟨f, hf, hfe⟩ := mem_image.mp h
    exact sym2_toFinset_injective hfe ▸ hf
  · exact mem_image_of_mem _

theorem mem_triangleVertexFamily_val_iff
    {V : Type*} [DecidableEq V] (A : TripleSystemOn V) (T : TripleOn V) :
    T.1 ∈ triangleVertexFamily A ↔ T ∈ A := by
  constructor
  · intro h
    obtain ⟨U, hU, hUT⟩ := mem_image.mp h
    exact Subtype.val_injective hUT ▸ hU
  · exact mem_image_of_mem _

theorem triangleVertexFamily_incident_card
    {V : Type*} [DecidableEq V] (A : TripleSystemOn V) (P : Finset V) :
    ((triangleVertexFamily A).filter (P ⊆ ·)).card = (A.filter (fun T ↦ P ⊆ T.1)).card := by
  have heq : (triangleVertexFamily A).filter (P ⊆ ·) =
      (A.filter (fun T ↦ P ⊆ T.1)).image Subtype.val := by
    ext S
    simp only [triangleVertexFamily, mem_filter, mem_image]
    constructor
    · rintro ⟨⟨T, hT, rfl⟩, hPS⟩
      exact ⟨T, ⟨hT, hPS⟩, rfl⟩
    · rintro ⟨T, ⟨hT, hPS⟩, rfl⟩
      exact ⟨⟨T, hT, rfl⟩, hPS⟩
  rw [heq, card_image_of_injective _ Subtype.val_injective]

theorem triangleVertexFamily_edge_card
    {V : Type*} [DecidableEq V] (A : TripleSystemOn V) (e : Sym2 V) (he : ¬ e.IsDiag) :
    ((triangleVertexFamily A).filter (e.toFinset ⊆ ·)).card =
      (A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card := by
  rw [triangleVertexFamily_incident_card]
  congr 1
  ext T
  simp only [mem_filter, mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T he]

theorem graphPairFamily_contains_triangle_pairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V)
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) :
    ∀ S ∈ triangleVertexFamily A, S.powersetCard 2 ⊆ graphPairFamily G := by
  intro S hS P hP
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hS
  have hm := mem_powersetCard.mp hP
  obtain ⟨v, w, hvw, rfl⟩ := card_eq_two.mp hm.2
  have he : s(v, w) ∈ tripleEdgeFinset T := mk_mem_tripleEdgeFinset_iff.mpr
    ⟨hm.1 (by simp), hm.1 (by simp), hvw⟩
  have himage := mem_image.mpr ⟨s(v, w), hA T hT he, Sym2.toFinset_mk_eq⟩
  exact himage

theorem triangleVertexFamily_decode_subset
    {V : Type*} [DecidableEq V] (A : TripleSystemOn V) (R : Finset (Finset V))
    (hR : R ⊆ triangleVertexFamily A) :
    ∃ B ⊆ A, triangleVertexFamily B = R := by
  refine ⟨A.filter (fun T ↦ T.1 ∈ R), filter_subset _ _, ?_⟩
  ext S
  simp only [triangleVertexFamily, mem_image, mem_filter]
  constructor
  · rintro ⟨T, ⟨hT, hTR⟩, rfl⟩
    exact hTR
  · intro hSR
    obtain ⟨T, hT, rfl⟩ := mem_image.mp (hR hSR)
    exact ⟨T, ⟨hT, hSR⟩, rfl⟩

end

end Erdos207
