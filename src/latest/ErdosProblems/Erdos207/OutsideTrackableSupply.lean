/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TrackedInitialSparsification
import ErdosProblems.Erdos207.PreliminaryEdgeSupply

/-!
# Pair-star supply for tracked initial prescriptions
-/

namespace Erdos207

open Finset

noncomputable section

/-- A currently uncovered trackable pair is alive by the outside-pair
survival invariant. -/
theorem availablePair_nonempty_of_trackable_uncovered
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {X : Finset V} {E : Finset (Sym2 V)}
    {S : GreedyStateOn V}
    (houtside : OutsideLeavePairsAlive H X S) :
    ∀ e ∈ outsideTrackablePart H X E,
      e ∈ greedyUncoveredEdges
        (graphEdges (SimpleGraph.completeGraph V)) S →
      (availableTrianglesContainingPair S e.toFinset).Nonempty := by
  intro e heTrack heUncovered
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hnotHedge : s(u, v) ∉ graphEdges H :=
        outsideTrackablePart_not_adj heTrack
      have hnotH : ¬ H.Adj u v := by
        intro huv
        exact hnotHedge (mem_graphEdges_iff.mpr huv)
      have hnotSub : ¬ s(u, v).toFinset ⊆ X :=
        outsideTrackablePart_not_both_mem heTrack
      have hnotBoth : ¬ (u ∈ X ∧ v ∈ X) := by
        intro huv
        apply hnotSub
        intro x hx
        simp only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact huv.1
        · exact huv.2
      have hnotCovered : ¬ (coveredGraph S.chosen).Adj u v := by
        intro hcovered
        exact (mem_sdiff.mp heUncovered).2
          (mem_graphEdges_iff.mpr hcovered)
      have hne : u ≠ v := by
        simpa only [Sym2.mk_isDiag_iff] using
          (outsideTrackablePart_offdiag H X E s(u, v) heTrack)
      have hleave : (leaveGraph S.chosen).Adj u v :=
        leaveGraph_adj.mpr ⟨hne, hnotCovered⟩
      simpa [PairAlive, Sym2.toFinset_mk_eq] using
        (houtside u v hnotH hnotBoth hleave)

/-- The pair floor supplies every edge needed by the retrospective event:
edges of pending prescribed triangles are alive because the triangle itself
is available, and tracked residual edges are alive by outside survival. -/
theorem pendingSurvivalEdges_supply_of_pairFloor_trackable
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {X : Finset V} {E : Finset (Sym2 V)}
    {S : GreedyStateOn V} {Q : TripleSystemOn V} {d : ℕ}
    (hfloor : HasAvailablePairFloor d S)
    (houtside : OutsideLeavePairsAlive H X S)
    (hQavailable : Q ⊆ S.available)
    (hBuncovered : outsideTrackablePart H X E ⊆
      greedyUncoveredEdges
        (graphEdges (SimpleGraph.completeGraph V)) S) :
    ∀ e ∈ pendingSurvivalEdges Q (outsideTrackablePart H X E),
      d ≤ (greedyChoicesCoveringEdge S e).card := by
  intro e he
  rw [pendingSurvivalEdges, mem_union] at he
  rcases he with heQ | heB
  · obtain ⟨T, hTQ, heT⟩ := mem_biUnion.mp heQ
    have hoff : ¬ e.IsDiag := not_isDiag_of_mem_tripleEdgeFinset heT
    rw [card_greedyChoicesCoveringEdge_eq_availablePair S e hoff]
    apply hfloor e.toFinset
      (Sym2.card_toFinset_of_not_isDiag e hoff)
    refine ⟨T, mem_availableTrianglesContainingPair_iff.mpr
      ⟨hQavailable hTQ, ?_⟩⟩
    exact (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag
      e T hoff).mp heT
  · have hoff : ¬ e.IsDiag :=
      outsideTrackablePart_offdiag H X E e heB
    rw [card_greedyChoicesCoveringEdge_eq_availablePair S e hoff]
    exact hfloor e.toFinset
      (Sym2.card_toFinset_of_not_isDiag e hoff)
      (availablePair_nonempty_of_trackable_uncovered
        houtside e heB (hBuncovered heB))

end

end Erdos207
