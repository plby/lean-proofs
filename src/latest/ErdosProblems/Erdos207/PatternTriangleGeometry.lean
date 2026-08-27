/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ProperPatternExtensions
import ErdosProblems.Erdos207.PairSharingIntersection

/-! # Distinct base edges and distinct vertical pairs -/

namespace Erdos207

open Finset

noncomputable section

theorem patternExtensionTriangle_erase_vertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (e : graphEdges Q) (u : V) (hu : u ∉ graphSupportFinset Q) :
    (patternExtensionTriangle Q e u hu).1.erase u = e.1.toFinset := by
  have hua : u ≠ e.1.out.1 := fun h ↦ hu (h ▸ (endpoint_mem_graphSupportFinset e.2).1)
  have hub : u ≠ e.1.out.2 := fun h ↦ hu (h ▸ (endpoint_mem_graphSupportFinset e.2).2)
  have he : e.1.toFinset = {e.1.out.1, e.1.out.2} := by
    conv_lhs => rw [← e.1.out_eq, Sym2.toFinset_mk_eq]
  rw [he]
  simp only [patternExtensionTriangle, thirdVertexTriple, tripleOfThree]
  ext x
  simp only [mem_erase, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hxu, rfl | rfl | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (hxu rfl).elim
  · rintro (rfl | rfl)
    · exact ⟨hua.symm, Or.inl rfl⟩
    · exact ⟨hub.symm, Or.inr (Or.inl rfl)⟩

theorem patternExtensionTriangle_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (u : V) (hu : u ∉ graphSupportFinset Q) :
    Function.Injective (fun e : graphEdges Q ↦ patternExtensionTriangle Q e u hu) := by
  intro e f hef
  have herase := congrArg (fun T : TripleOn V ↦ T.1.erase u) hef
  rw [patternExtensionTriangle_erase_vertex, patternExtensionTriangle_erase_vertex] at herase
  apply Subtype.ext
  apply Sym2.ext
  intro x
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, herase]

theorem verticalPair_ne_of_vertices_ne
    {V : Type*} [DecidableEq V] {u x y : V} (hxy : x ≠ y) :
    ({u, x} : Finset V) ≠ {u, y} := by
  intro h
  have hxmem : x ∈ ({u, y} : Finset V) := h ▸ mem_insert_of_mem (mem_singleton_self x)
  have hymem : y ∈ ({u, x} : Finset V) := h.symm ▸ mem_insert_of_mem (mem_singleton_self y)
  have hx : x = u ∨ x = y := by simpa only [mem_insert, mem_singleton] using hxmem
  have hy : y = u ∨ y = x := by simpa only [mem_insert, mem_singleton] using hymem
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · exact hxy (hx.trans hy.symm)
    · exact hxy hy.symm
  · exact hxy hx

theorem card_verticalPairStars_inter_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) {u x y : V} (hux : u ≠ x) (huy : u ≠ y) (hxy : x ≠ y) :
    (availableTrianglesContainingPair S {u, x} ∩
      availableTrianglesContainingPair S {u, y}).card ≤ 1 := by
  have huxcard : ({u, x} : Finset V).card = 2 := by simp [hux]
  have huycard : ({u, y} : Finset V).card = 2 := by simp [huy]
  apply (card_le_card ?_).trans
    (card_triplesContaining_distinct_pairs_le_one huxcard huycard
      (verticalPair_ne_of_vertices_ne (u := u) hxy))
  intro T hT
  exact mem_inter.mpr
    ⟨mem_universeTriplesContainingPair_iff.mpr
      (mem_availableTrianglesContainingPair_iff.mp (mem_inter.mp hT).1).2,
     mem_universeTriplesContainingPair_iff.mpr
      (mem_availableTrianglesContainingPair_iff.mp (mem_inter.mp hT).2).2⟩

end

end Erdos207
