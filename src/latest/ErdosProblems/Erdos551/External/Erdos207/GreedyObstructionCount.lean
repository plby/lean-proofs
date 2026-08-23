/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.GreedyObstruction

/-!
# Exact counts for third-vertex obstructions

The map from a third vertex to its triangle through a fixed pair is
injective.  Moreover, when the fixed pair is uncovered, failure of the
packing condition is witnessed by adjacency of the third vertex to one of
the endpoints in the already covered graph.  These observations isolate the
two numerical estimates needed in every cover-down step.
-/

namespace Erdos207

open Finset

@[simp]
lemma third_mem_thirdVertexTriple
    {V : Type*} [DecidableEq V] {u v : V} (huv : u ≠ v)
    (w : ThirdVertex u v) : w.1 ∈ (thirdVertexTriple huv w).1 := by
  simp [thirdVertexTriple, tripleOfThree]

/-- For a fixed pair, a triangle determines its third vertex. -/
lemma thirdVertexTriple_injective
    {V : Type*} [DecidableEq V] {u v : V} (huv : u ≠ v) :
    Function.Injective (thirdVertexTriple huv) := by
  intro w z hwz
  apply Subtype.ext
  have hw : w.1 ∈ (thirdVertexTriple huv z).1 := by
    rw [← hwz]
    exact third_mem_thirdVertexTriple huv w
  simp [thirdVertexTriple, tripleOfThree] at hw
  rcases hw with hwu | hwv | hwz
  · exact (w.2.1 hwu).elim
  · exact (w.2.2 hwv).elim
  · exact hwz

/-- Avoidance of a graph by the triangle through `uv` is exactly avoidance
of its three displayed pairs. -/
lemma triangleAvoidsGraph_thirdVertexTriple_iff
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {u v : V} (huv : u ≠ v) (w : ThirdVertex u v) :
    TriangleAvoidsGraph G (thirdVertexTriple huv w) ↔
      ¬G.Adj u v ∧ ¬G.Adj u w.1 ∧ ¬G.Adj v w.1 := by
  constructor
  · intro h
    exact ⟨h u (left_mem_thirdVertexTriple huv w)
        v (right_mem_thirdVertexTriple huv w) huv,
      h u (left_mem_thirdVertexTriple huv w)
        w.1 (third_mem_thirdVertexTriple huv w) w.2.1.symm,
      h v (right_mem_thirdVertexTriple huv w)
        w.1 (third_mem_thirdVertexTriple huv w) w.2.2.symm⟩
  · rintro ⟨huvG, huwG, hvwG⟩ x hx y hy hxy hxyG
    simp [thirdVertexTriple, tripleOfThree] at hx hy
    rcases hx with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl
    · exact hxy rfl
    · exact huvG hxyG
    · exact huwG hxyG
    · exact huvG (by simpa only [SimpleGraph.adj_comm] using hxyG)
    · exact hxy rfl
    · exact hvwG hxyG
    · exact huwG (by simpa only [SimpleGraph.adj_comm] using hxyG)
    · exact hvwG (by simpa only [SimpleGraph.adj_comm] using hxyG)
    · exact hxy rfl

/-- If `uv` is uncovered, every edge-blocked third vertex is a covered
neighbor of at least one endpoint. -/
lemma edgeBlockedThirdVertex_mem_neighbor_union
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} {u v : V}
    (huv : (leaveGraph P).Adj u v) {w : ThirdVertex u v}
    (hw : w ∈ edgeBlockedThirdVertices A P huv.ne) :
    w.1 ∈ (coveredGraph P).neighborFinset u ∪
      (coveredGraph P).neighborFinset v := by
  rw [mem_union, SimpleGraph.mem_neighborFinset,
    SimpleGraph.mem_neighborFinset]
  have hnotAvoid := (mem_edgeBlockedThirdVertices_iff.mp hw).2
  rw [triangleAvoidsGraph_thirdVertexTriple_iff] at hnotAvoid
  have huvNot : ¬(coveredGraph P).Adj u v := by
    intro hcovered
    exact huv.2 (coveredGraph_adj.mp hcovered)
  tauto

/-- The packing obstruction count is bounded by the union of the two
covered neighborhoods.  Later quasirandom estimates are plugged into this
exact deterministic inequality. -/
theorem card_edgeBlockedThirdVertices_le_neighbor_union
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} {u v : V}
    (huv : (leaveGraph P).Adj u v) :
    (edgeBlockedThirdVertices A P huv.ne).card ≤
      ((coveredGraph P).neighborFinset u ∪
        (coveredGraph P).neighborFinset v).card := by
  let e : ThirdVertex u v ↪ V := Function.Embedding.subtype _
  have hsub : (edgeBlockedThirdVertices A P huv.ne).map e ⊆
      (coveredGraph P).neighborFinset u ∪
        (coveredGraph P).neighborFinset v := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hw
    exact edgeBlockedThirdVertex_mem_neighbor_union huv hz
  simpa using card_le_card hsub

/-- A coarser but convenient degree-sum version of the obstruction bound. -/
theorem card_edgeBlockedThirdVertices_le_degree_add
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} {u v : V}
    (huv : (leaveGraph P).Adj u v) :
    (edgeBlockedThirdVertices A P huv.ne).card ≤
      (coveredGraph P).degree u + (coveredGraph P).degree v := by
  calc
    (edgeBlockedThirdVertices A P huv.ne).card ≤
        ((coveredGraph P).neighborFinset u ∪
          (coveredGraph P).neighborFinset v).card :=
      card_edgeBlockedThirdVertices_le_neighbor_union huv
    _ ≤ ((coveredGraph P).neighborFinset u).card +
          ((coveredGraph P).neighborFinset v).card :=
      card_union_le _ _
    _ = (coveredGraph P).degree u + (coveredGraph P).degree v := by
      rw [SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.card_neighborFinset_eq_degree]

/-- The two classes of obstructions can always be estimated separately. -/
lemma card_blocked_union_le_add
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) :
    (edgeBlockedThirdVertices A P huv ∪
      forbiddenBlockedThirdVertices F A P huv).card ≤
      (edgeBlockedThirdVertices A P huv).card +
        (forbiddenBlockedThirdVertices F A P huv).card :=
  card_union_le _ _

/-- Degree control for the packing obstruction, together with a direct
bound on forbidden completions, is enough to extend every outside leave
edge. -/
theorem outsideLeaveEdgesLegallyExtendable_of_degree_forbidden_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {H : SimpleGraph V} {X : Finset V}
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F)
    (hcount : ∀ ⦃u v : V⦄
      (huv : (graphDifference (leaveGraph P) H).Adj u v),
      (u ∉ X ∨ v ∉ X) →
      (coveredGraph P).degree u + (coveredGraph P).degree v +
          (forbiddenBlockedThirdVertices F A P huv.1.ne).card <
        (candidateThirdVertices A huv.1.ne).card) :
    OutsideLeaveEdgesLegallyExtendable F A P H X := by
  apply outsideLeaveEdgesLegallyExtendable_of_blocked_lt hpacking havoid
  intro u v huv houtside
  have hedge := card_edgeBlockedThirdVertices_le_degree_add
    (A := A) (P := P) huv.1
  have hunion := card_blocked_union_le_add
    (F := F) (A := A) (P := P) huv.1.ne
  have htotal :
      (edgeBlockedThirdVertices A P huv.1.ne ∪
        forbiddenBlockedThirdVertices F A P huv.1.ne).card ≤
      (coveredGraph P).degree u + (coveredGraph P).degree v +
        (forbiddenBlockedThirdVertices F A P huv.1.ne).card := by
    omega
  exact htotal.trans_lt (hcount huv houtside)

/-- The preceding pointwise numerical inequality is the exact deterministic
input needed to turn maximality into support of the final remainder. -/
theorem graphSupportedOn_of_maximal_degree_forbidden_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {H : SimpleGraph V} {X : Finset V}
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F)
    (hmax : legalAvailable F P A = ∅)
    (hcount : ∀ ⦃u v : V⦄
      (huv : (graphDifference (leaveGraph P) H).Adj u v),
      (u ∉ X ∨ v ∉ X) →
      (coveredGraph P).degree u + (coveredGraph P).degree v +
          (forbiddenBlockedThirdVertices F A P huv.1.ne).card <
        (candidateThirdVertices A huv.1.ne).card) :
    GraphSupportedOn (graphDifference (leaveGraph P) H) (X : Set V) := by
  apply graphSupportedOn_of_maximal_legal hmax
  exact outsideLeaveEdgesLegallyExtendable_of_degree_forbidden_lt
    hpacking havoid hcount

end Erdos207
