/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.InfiniteColouredOccurrenceEndpointBalance

/-!
# Exposed warp boundaries cannot be internal occurrences

An occurrence outside the reference carrier has only forward adjacent
steps. Hence a forward initial can only be the first vertex, and a forward
terminal can only be the last vertex. The infinite case has no last vertex.
No simplicity or interval-safeness assumption is needed.
-/

namespace Erdos599.Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

namespace FiniteColouredOccurrenceWord

/-- Every noninitial occurrence is an endpoint of a literally owned edge. -/
theorem vertexSet_subset_forward_union_reference
    (Q : FiniteColouredOccurrenceWord W Y)
    (hfirst : Q.vertex 0 ∈ Gamma.vertexSet W ∪ Gamma.vertexSet Y) :
    Q.vertexSet ⊆ Gamma.vertexSet W ∪ Gamma.vertexSet Y := by
  rintro x ⟨i, rfl⟩
  cases i using Fin.cases with
  | zero => exact hfirst
  | succ i =>
    have he := Q.actualEdge_spec i
    cases hd : Q.direction i with
    | forward =>
      simp only [hd] at he
      exact Or.inl (familyEdges_subset_vertexSet_prod W he).2
    | backward =>
      simp only [hd] at he
      exact Or.inr (familyEdges_subset_vertexSet_prod Y he).1

theorem eq_first_of_initial_of_mem_vertexSet
    (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    {x : V} (hx : x ∈ Gamma.initialSet W) (hxOff : x ∉ Gamma.vertexSet Y)
    (hxQ : x ∈ Q.vertexSet) : x = Q.vertex 0 := by
  rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfinite] at hx
  obtain ⟨i, rfl⟩ := hxQ
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    have he := Q.actualEdge_spec i
    cases hd : Q.direction i with
    | forward =>
      simp only [hd] at he
      exact False.elim (hx.2 ⟨Q.vertex i.castSucc, he⟩)
    | backward =>
      simp only [hd] at he
      exact False.elim (hxOff (familyEdges_subset_vertexSet_prod Y he).1)

theorem eq_last_of_terminal_of_mem_vertexSet
    (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    {x : V} (hx : x ∈ Gamma.terminalFrontier W) (hxOff : x ∉ Gamma.vertexSet Y)
    (hxQ : x ∈ Q.vertexSet) : x = Q.vertex (Fin.last Q.length) := by
  rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfinite] at hx
  obtain ⟨i, rfl⟩ := hxQ
  cases i using Fin.lastCases with
  | last => rfl
  | cast i =>
    have he := Q.actualEdge_spec i
    cases hd : Q.direction i with
    | forward =>
      simp only [hd] at he
      exact False.elim (hx.2 ⟨Q.vertex i.succ, he⟩)
    | backward =>
      simp only [hd] at he
      exact False.elim (hxOff (familyEdges_subset_vertexSet_prod Y he).2)

/-- If every visited cut vertex is an exposed forward boundary, the finite
word meets that cut only at its first and last vertices. -/
theorem vertexSet_inter_subset_endpoints
    (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    {X : Set V} (hX : Disjoint X (Gamma.vertexSet Y))
    (hboundary : Q.vertexSet ∩ X ⊆
      Gamma.initialSet W ∪ Gamma.terminalFrontier W) :
    Q.vertexSet ∩ X ⊆ {Q.vertex 0, Q.vertex (Fin.last Q.length)} := by
  intro x hx
  have hxOff := Set.disjoint_left.mp hX hx.2
  rcases hboundary hx with hinit | hterminal
  · exact Or.inl (Q.eq_first_of_initial_of_mem_vertexSet hW hWfinite hinit hxOff hx.1)
  · exact Or.inr (Q.eq_last_of_terminal_of_mem_vertexSet hW hWfinite
      hterminal hxOff hx.1)

end FiniteColouredOccurrenceWord

namespace InfiniteColouredOccurrenceWord

/-- Every infinite occurrence has a next literally owned edge. -/
theorem vertexSet_subset_forward_union_reference
    (Q : InfiniteColouredOccurrenceWord W Y) :
    Q.vertexSet ⊆ Gamma.vertexSet W ∪ Gamma.vertexSet Y := by
  rintro x ⟨i, rfl⟩
  have he := Q.actualEdge_spec i
  cases hd : Q.direction i with
  | forward =>
    simp only [hd] at he
    exact Or.inl (familyEdges_subset_vertexSet_prod W he).1
  | backward =>
    simp only [hd] at he
    exact Or.inr (familyEdges_subset_vertexSet_prod Y he).2

theorem eq_first_of_initial_of_mem_vertexSet
    (Q : InfiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    {x : V} (hx : x ∈ Gamma.initialSet W) (hxOff : x ∉ Gamma.vertexSet Y)
    (hxQ : x ∈ Q.vertexSet) : x = Q.vertex 0 := by
  rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfinite] at hx
  obtain ⟨i, rfl⟩ := hxQ
  cases i with
  | zero => rfl
  | succ i =>
    have he := Q.actualEdge_spec i
    cases hd : Q.direction i with
    | forward =>
      simp only [hd] at he
      exact False.elim (hx.2 ⟨Q.vertex i, he⟩)
    | backward =>
      simp only [hd] at he
      exact False.elim (hxOff (familyEdges_subset_vertexSet_prod Y he).1)

theorem not_mem_vertexSet_of_terminal
    (Q : InfiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    {x : V} (hx : x ∈ Gamma.terminalFrontier W) (hxOff : x ∉ Gamma.vertexSet Y) :
    x ∉ Q.vertexSet := by
  rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfinite] at hx
  rintro ⟨i, rfl⟩
  have he := Q.actualEdge_spec i
  cases hd : Q.direction i with
  | forward =>
    simp only [hd] at he
    exact hx.2 ⟨Q.vertex (i + 1), he⟩
  | backward =>
    simp only [hd] at he
    exact hxOff (familyEdges_subset_vertexSet_prod Y he).2

/-- The infinite counterpart has no terminal exception. -/
theorem vertexSet_inter_subset_initial
    (Q : InfiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    {X : Set V} (hX : Disjoint X (Gamma.vertexSet Y))
    (hboundary : Q.vertexSet ∩ X ⊆
      Gamma.initialSet W ∪ Gamma.terminalFrontier W) :
    Q.vertexSet ∩ X ⊆ {Q.vertex 0} := by
  intro x hx
  have hxOff := Set.disjoint_left.mp hX hx.2
  rcases hboundary hx with hinit | hterminal
  · exact Q.eq_first_of_initial_of_mem_vertexSet hW hWfinite hinit hxOff hx.1
  · exact False.elim (Q.not_mem_vertexSet_of_terminal hW hWfinite hterminal hxOff hx.1)

end InfiniteColouredOccurrenceWord

#print axioms FiniteColouredOccurrenceWord.vertexSet_inter_subset_endpoints
#print axioms InfiniteColouredOccurrenceWord.vertexSet_inter_subset_initial

end Erdos599.Alternating
