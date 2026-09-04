/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PathCover
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Decomposing finite even graphs into cycles

This supplies the graph-theoretic first step of KSSS Lemma 4.3.  Mathlib's
Euler-trail file intentionally does not contain the converse Euler theorem,
so we use the equivalent induction which repeatedly removes a simple cycle.
-/

namespace Erdos207

open Finset

noncomputable section

def connectedComponentNeighborEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : G.ConnectedComponent) (v : c) :
    c.toSimpleGraph.neighborSet v ≃ G.neighborSet v.1 where
  toFun w :=
    ⟨w.1.1, (c.toSimpleGraph_adj v.2 w.1.2).mp w.2⟩
  invFun w := by
    have hwc : w.1 ∈ c.supp := c.mem_supp_of_adj_mem_supp v.2 w.2
    exact ⟨⟨w.1, hwc⟩, (c.toSimpleGraph_adj v.2 hwc).mpr w.2⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

lemma connectedComponent_degree_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : G.ConnectedComponent) [Fintype c]
    [DecidableRel c.toSimpleGraph.Adj] (v : c) :
    c.toSimpleGraph.degree v = G.degree v.1 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree,
    Fintype.card_congr (connectedComponentNeighborEquiv c v)]

/-- A finite graph with all degrees even cannot be an acyclic nonempty
graph: a nontrivial tree component would have a degree-one leaf. -/
lemma not_isAcyclic_of_even_degree_of_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v))
    {u v : V} (huv : G.Adj u v) : ¬G.IsAcyclic := by
  intro hac
  let c : G.ConnectedComponent := G.connectedComponentMk u
  have hu : u ∈ c.supp := by rfl
  have hv : v ∈ c.supp := c.mem_supp_of_adj_mem_supp hu huv
  have huvne : u ≠ v := G.ne_of_adj huv
  let : Fintype c := Fintype.ofFinite _
  let : DecidableRel c.toSimpleGraph.Adj := Classical.decRel _
  let : Nontrivial c :=
    ⟨⟨⟨u, hu⟩, ⟨v, hv⟩, by
      intro h
      apply huvne
      exact congrArg Subtype.val h⟩⟩
  have htree : c.toSimpleGraph.IsTree := hac.isTree_connectedComponent c
  obtain ⟨w, hw⟩ := htree.exists_vert_degree_one_of_nontrivial
  have hdegree : G.degree w.1 = 1 := by
    rw [← connectedComponent_degree_eq c w]
    exact hw
  obtain ⟨d, hd⟩ := heven w.1
  omega

/-- Every nonempty finite even graph contains a simple cycle. -/
theorem exists_isCycle_of_even_degree_of_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v))
    {u v : V} (huv : G.Adj u v) :
    ∃ w : V, ∃ p : G.Walk w w, p.IsCycle := by
  have hnacyclic := not_isAcyclic_of_even_degree_of_edge heven huv
  simp only [SimpleGraph.IsAcyclic] at hnacyclic
  push_neg at hnacyclic
  exact hnacyclic

lemma degree_eq_zero_or_two_of_isCycles
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : H.IsCycles) (v : V) : H.degree v = 0 ∨ H.degree v = 2 := by
  by_cases hv : (H.neighborSet v).Nonempty
  · right
    rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    exact hH hv
  · left
    rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard,
      Set.ncard_eq_zero]
    exact Set.not_nonempty_iff_eq_empty.mp hv

/-- Removing a graph of vertex-degrees zero or two from an even graph
preserves evenness.  The subgraph hypothesis makes the degree subtraction
literal rather than merely an inclusion-exclusion statement. -/
lemma even_degree_sdiff_of_isCycles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (heven : ∀ v, Even (G.degree v)) (hHG : H ≤ G) (hH : H.IsCycles) :
    ∀ v, Even ((G \ H).degree v) := by
  intro v
  have hneighbors : H.neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hHG hw
  have hdegree : (G \ H).degree v = G.degree v - H.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_sdiff, Finset.card_sdiff_of_subset hneighbors,
      SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree]
  rw [hdegree]
  rcases degree_eq_zero_or_two_of_isCycles H hH v with hv | hv
  · simp [hv, heven v]
  · rw [hv]
    have hdegree_le : H.degree v ≤ G.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree,
        ← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_le_card hneighbors
    apply (Nat.even_sub (by simpa [hv] using hdegree_le)).mpr
    exact iff_of_true (heven v) even_two

/-- The spanning graph of a walk only uses edges of its ambient graph. -/
lemma walkSpanningCoe_le
    {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.toSubgraph.spanningCoe ≤ G :=
  p.toSubgraph.spanningCoe_le

/-- A proof object for the recursive cycle-removal decomposition of a finite
graph.  Every `step` stores one simple cycle and then decomposes exactly the
graph left after deleting that cycle's edges. -/
inductive CycleDecomposition {V : Type*} : SimpleGraph V → Type _ where
  | empty : CycleDecomposition (⊥ : SimpleGraph V)
  | step {G : SimpleGraph V} {v : V} (p : G.Walk v v) (hp : p.IsCycle)
      (tail : CycleDecomposition (G \ p.toSubgraph.spanningCoe)) :
      CycleDecomposition G

namespace CycleDecomposition

/-- Number of simple cycles removed by a decomposition. -/
def cycleCount {V : Type*} {G : SimpleGraph V} : CycleDecomposition G → ℕ
  | .empty => 0
  | .step _ _ tail => tail.cycleCount + 1

/-- A cycle-removal decomposition uses no more cycles than the original
graph has edges. -/
lemma cycleCount_le_edgeNcard
    {V : Type*} [Finite V] {G : SimpleGraph V} (D : CycleDecomposition G) :
    D.cycleCount ≤ G.edgeSet.ncard := by
  induction D with
  | empty => simp [cycleCount]
  | @step G v p hp tail ih =>
      let H : SimpleGraph V := p.toSubgraph.spanningCoe
      have hHne : H ≠ ⊥ := by
        rw [SimpleGraph.ne_bot_iff_exists_adj]
        exact ⟨v, p.snd, by
          change p.toSubgraph.Adj v p.snd
          exact p.toSubgraph_adj_snd hp.not_nil⟩
      have hHG : H ≤ G := walkSpanningCoe_le p
      have hlt : G \ H < G := by
        apply sdiff_lt_left.mpr
        intro hdisjoint
        obtain ⟨x, y, hxy⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hHne
        exact (SimpleGraph.disjoint_left.mp hdisjoint x y hxy) (hHG hxy)
      have hncard :
          (G \ p.toSubgraph.spanningCoe).edgeSet.ncard < G.edgeSet.ncard := by
        simpa only [H] using
          Set.ncard_lt_ncard (SimpleGraph.edgeSet_strict_mono hlt)
      simp only [cycleCount]
      omega

/-- On at least two vertices, the number of cycles in a decomposition is
strictly less than the square of the vertex count.  This is the coarse bound
used to allocate the two path-cover slots attached to each cycle. -/
lemma cycleCount_lt_card_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hV : 2 ≤ Fintype.card V) (D : CycleDecomposition G) :
    D.cycleCount < (Fintype.card V) ^ 2 := by
  have hGtop : G ≤ SimpleGraph.completeGraph V := OrderTop.le_top G
  have hedge : G.edgeFinset.card ≤
      (SimpleGraph.completeGraph V).edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hGtop)
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at hedge
  have hcount := D.cycleCount_le_edgeNcard
  have hedgeNcard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.edgeFinset_card]
  rw [hedgeNcard] at hcount
  have hchoose : (Fintype.card V).choose 2 < (Fintype.card V) ^ 2 := by
    rw [Nat.choose_two_right]
    calc
      Fintype.card V * (Fintype.card V - 1) / 2 ≤
          Fintype.card V * (Fintype.card V - 1) := Nat.div_le_self _ _
      _ < (Fintype.card V) ^ 2 := by
        have hpos : 0 < Fintype.card V := by omega
        have hpred : Fintype.card V - 1 < Fintype.card V := by omega
        simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hpred hpos
  omega

end CycleDecomposition

/-- The cycle-removal process is well founded because every chosen cycle has
an edge, so deleting it strictly lowers the finite edge count. -/
theorem exists_cycleDecomposition_of_even_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v)) : Nonempty (CycleDecomposition G) := by
  by_cases hG : G = ⊥
  · subst G
    exact ⟨CycleDecomposition.empty⟩
  · obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG
    obtain ⟨w, p, hp⟩ := exists_isCycle_of_even_degree_of_edge heven huv
    let H : SimpleGraph V := p.toSubgraph.spanningCoe
    let : DecidableRel H.Adj := Classical.decRel _
    have hHG : H ≤ G := walkSpanningCoe_le p
    have hHcycles : H.IsCycles := hp.isCycles_spanningCoe_toSubgraph
    let R : SimpleGraph V := G \ H
    have hReven : ∀ x, Even (R.degree x) :=
      even_degree_sdiff_of_isCycles G H heven hHG hHcycles
    have hHne : H ≠ ⊥ := by
      rw [SimpleGraph.ne_bot_iff_exists_adj]
      exact ⟨w, p.snd, by
        change p.toSubgraph.Adj w p.snd
        exact p.toSubgraph_adj_snd hp.not_nil⟩
    have hRlt : R < G := by
      apply sdiff_lt_left.mpr
      intro hdisjoint
      obtain ⟨x, y, hxy⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hHne
      exact (SimpleGraph.disjoint_left.mp hdisjoint x y hxy) (hHG hxy)
    have hcardR : R.edgeSet.ncard < G.edgeSet.ncard :=
      Set.ncard_lt_ncard (SimpleGraph.edgeSet_strict_mono hRlt)
    obtain ⟨tail⟩ := exists_cycleDecomposition_of_even_degree R hReven
    exact ⟨CycleDecomposition.step p hp tail⟩
termination_by G.edgeSet.ncard
decreasing_by exact hcardR

end

end Erdos207
