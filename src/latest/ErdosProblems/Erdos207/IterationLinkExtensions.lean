/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationReserveCandidates
import ErdosProblems.Erdos207.PairedBisectionDegreeScalar

/-!
# Link degrees as iteration-pattern extension counts

The one-edge and two-edge-star instances of iteration typicality are the
degree and codegree estimates for an available link graph.  The definition
of `iterationExtensionVertices` permits a pattern vertex itself to be an
extension.  For a one-edge pattern with its center outside the target set,
this creates at most the other endpoint as a spurious extension, hence the
exact additive loss one proved below.  For the codegree upper bound only the
opposite inclusion is needed.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The two-edge star used to measure common link neighbors. -/
def linkStarGraph {V : Type*} [DecidableEq V] (center x y : V) :
    SimpleGraph V :=
  SimpleGraph.edge center x ⊔ SimpleGraph.edge center y

lemma graphEdges_linkStarGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {center x y : V} (hcx : center ≠ x) (hcy : center ≠ y) :
    graphEdges (linkStarGraph center x y) = {s(center, x), s(center, y)} := by
  ext e
  rw [mem_graphEdges_iff]
  simp only [linkStarGraph, SimpleGraph.edgeSet_sup, Set.mem_union,
    SimpleGraph.edgeSet_edge, Set.mem_sdiff, Set.mem_singleton_iff,
    Sym2.mem_diagSet]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_singleton_self _)
  · intro he
    rcases mem_insert.mp he with rfl | he
    · exact Or.inl ⟨rfl, by simpa [Sym2.mk_isDiag_iff] using hcx⟩
    · have : e = s(center, y) := mem_singleton.mp he
      subst e
      exact Or.inr ⟨rfl, by simpa [Sym2.mk_isDiag_iff] using hcy⟩

lemma graphSupportFinset_linkStarGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {center x y : V} (hcx : center ≠ x) (hcy : center ≠ y) :
    graphSupportFinset (linkStarGraph center x y) = {center, x, y} := by
  ext z
  rw [mem_graphSupportFinset_iff]
  simp only [linkStarGraph, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
    mem_insert, mem_singleton]
  constructor
  · rintro ⟨w, (⟨h | h, _⟩ | ⟨h | h, _⟩)⟩
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inl h.1
    · exact Or.inr (Or.inr h.1)
  · rintro (rfl | rfl | rfl)
    · exact ⟨x, Or.inl ⟨Or.inl ⟨rfl, rfl⟩, hcx⟩⟩
    · exact ⟨center, Or.inl ⟨Or.inr ⟨rfl, rfl⟩, hcx.symm⟩⟩
    · exact ⟨center, Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hcy.symm⟩⟩

lemma graphSupportFinset_linkStarGraph_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {center x y : V} (hcx : center ≠ x) (hcy : center ≠ y)
    (hxy : x ≠ y) :
    (graphSupportFinset (linkStarGraph center x y)).card = 3 := by
  rw [graphSupportFinset_linkStarGraph hcx hcy]
  simp [hcx, hcy, hxy]

lemma linkStarGraph_le
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {center x y : V} (hcx : G.Adj center x) (hcy : G.Adj center y) :
    linkStarGraph center x y ≤ G := by
  intro u v huv
  rw [linkStarGraph, SimpleGraph.sup_adj] at huv
  rcases huv with huv | huv
  · exact (SimpleGraph.edge_le_iff G).mpr (Or.inr hcx) huv
  · exact (SimpleGraph.edge_le_iff G).mpr (Or.inr hcy) huv

lemma linkStarGraph_supportedOn
    {V : Type*} [DecidableEq V] {U : Finset V}
    {center x y : V} (hc : center ∈ U) (hx : x ∈ U) (hy : y ∈ U) :
    GraphSupportedOn (linkStarGraph center x y) (U : Set V) := by
  intro u v huv
  rw [linkStarGraph, SimpleGraph.sup_adj] at huv
  rcases huv with huv | huv
  · exact edge_graphSupportedOn hc hx huv
  · exact edge_graphSupportedOn hc hy huv

/-- Every genuine ambient link neighbor is a one-edge extension vertex. -/
lemma ambientLinkNeighborsIn_subset_iterationExtensionVertices_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    {center x : V} (hcx : center ≠ x)
    (A : TripleSystemOn V) (U : Finset V) :
    ambientLinkNeighborsIn center A U x ⊆
      iterationExtensionVertices A (SimpleGraph.edge center x) U := by
  intro w hw
  obtain ⟨hwU, T, hTA, hTval⟩ :=
    mem_ambientLinkNeighborsIn_iff.mp hw
  apply mem_iterationExtensionVertices_iff.mpr
  refine ⟨hwU, ?_⟩
  intro e he
  rw [graphEdges_edge hcx] at he
  have heq : e = s(center, x) := mem_singleton.mp he
  subst e
  refine ⟨T, hTA, ?_, ?_⟩
  · rw [hTval]
    simp
  · rw [mk_mem_tripleEdgeFinset_iff, hTval]
    simp [hcx]

/-- If the center is outside the target set, every one-edge extension is
either a genuine ambient link neighbor or the other pattern endpoint. -/
lemma iterationExtensionVertices_edge_subset_insert_ambient
    {V : Type*} [Fintype V] [DecidableEq V]
    {center x : V} (hcx : center ≠ x)
    (A : TripleSystemOn V) (U : Finset V) (hcenter : center ∉ U) :
    iterationExtensionVertices A (SimpleGraph.edge center x) U ⊆
      insert x (ambientLinkNeighborsIn center A U x) := by
  intro w hw
  by_cases hwx : w = x
  · subst w
    exact mem_insert_self _ _
  · apply mem_insert_of_mem
    have hwdata := mem_iterationExtensionVertices_iff.mp hw
    have hwc : w ≠ center := by
      intro h
      subst w
      exact hcenter hwdata.1
    have hedge : s(center, x) ∈
        graphEdges (SimpleGraph.edge center x) := by
      rw [graphEdges_edge hcx]
      simp
    obtain ⟨T, hTA, hwT, heT⟩ := hwdata.2 _ hedge
    have hends := mk_mem_tripleEdgeFinset_iff.mp heT
    have hsub : {center, x, w} ⊆ T.1 := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hends.1
      · exact hends.2.1
      · exact hwT
    have hsetcard : ({center, x, w} : Finset V).card = 3 := by
      have hn : center ∉ ({x, w} : Finset V) := by
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨hcx, Ne.symm hwc⟩
      rw [card_insert_of_notMem hn, card_pair (Ne.symm hwx)]
    have hval : T.1 = {center, x, w} := by
      symm
      exact eq_of_subset_of_card_le hsub (by rw [T.2, hsetcard])
    exact mem_ambientLinkNeighborsIn_iff.mpr
      ⟨hwdata.1, ⟨T, hTA, hval⟩⟩

/-- The one-edge extension count exceeds the ambient link degree by at most
one. -/
lemma card_iterationExtensionVertices_edge_le_ambient_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {center x : V} (hcx : center ≠ x)
    (A : TripleSystemOn V) (U : Finset V) (hcenter : center ∉ U) :
    (iterationExtensionVertices A (SimpleGraph.edge center x) U).card ≤
      (ambientLinkNeighborsIn center A U x).card + 1 := by
  calc
    (iterationExtensionVertices A (SimpleGraph.edge center x) U).card ≤
        (insert x (ambientLinkNeighborsIn center A U x)).card :=
      card_le_card
        (iterationExtensionVertices_edge_subset_insert_ambient hcx A U hcenter)
    _ ≤ (ambientLinkNeighborsIn center A U x).card + 1 :=
      card_insert_le _ _

/-- A genuine common ambient link neighbor extends the two-edge star. -/
lemma ambientLinkCommonNeighborsIn_subset_iterationExtensionVertices_star
    {V : Type*} [Fintype V] [DecidableEq V]
    {center x y : V} (hcx : center ≠ x) (hcy : center ≠ y)
    (A : TripleSystemOn V) (U : Finset V) :
    ambientLinkCommonNeighborsIn center A U x y ⊆
      iterationExtensionVertices A (linkStarGraph center x y) U := by
  intro w hw
  have hwdata := mem_ambientLinkCommonNeighborsIn_iff.mp hw
  apply mem_iterationExtensionVertices_iff.mpr
  refine ⟨hwdata.1, ?_⟩
  intro e he
  rw [graphEdges_linkStarGraph hcx hcy] at he
  rcases mem_insert.mp he with he | he
  · subst e
    obtain ⟨T, hTA, hTval⟩ := hwdata.2.1
    refine ⟨T, hTA, ?_, ?_⟩
    · rw [hTval]
      simp
    · rw [mk_mem_tripleEdgeFinset_iff, hTval]
      simp [hcx]
  · have heq : e = s(center, y) := mem_singleton.mp he
    subst e
    obtain ⟨T, hTA, hTval⟩ := hwdata.2.2
    refine ⟨T, hTA, ?_, ?_⟩
    · rw [hTval]
      simp
    · rw [mk_mem_tripleEdgeFinset_iff, hTval]
      simp [hcy]

end

end Erdos207
