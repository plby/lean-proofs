/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryEdgeSupply
import ErdosProblems.Erdos207.OutsidePairSurvival

/-!
# Outside-pair survival supplies every preliminary crossing edge

If the preliminary graph is edge-disjoint from the fixed absorber graph,
then each of its still-uncovered crossing edges is an eligible outside leave
pair.  The outside-survival invariant therefore makes its available pair
star nonempty, and the pair floor supplies the quantitative choice count.
-/

namespace Erdos207

open Finset

noncomputable section

theorem availablePair_nonempty_of_outsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    {H G : SimpleGraph V} {X : Finset V} {S : GreedyStateOn V}
    (hHG : Disjoint H G) (houtside : OutsideLeavePairsAlive H X S) :
    ∀ e ∈ greedyUncoveredEdges (crossingEdges G X) S,
      (availableTrianglesContainingPair S e.toFinset).Nonempty := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hecross : s(u, v) ∈ crossingEdges G X := (mem_sdiff.mp he).1
      have hGedge : s(u, v) ∈ G.edgeSet :=
        (mem_crossingEdges_iff.mp hecross).1
      have hG : G.Adj u v := by
        change G.Adj u v at hGedge
        exact hGedge
      have hcross :
          (u ∈ X ∧ v ∉ X) ∨ (v ∈ X ∧ u ∉ X) :=
        isCrossingEdge_mk_iff.mp (mem_crossingEdges_iff.mp hecross).2
      have hnotBoth : ¬ (u ∈ X ∧ v ∈ X) := by aesop
      have hnotH : ¬ H.Adj u v := by
        intro hH
        exact SimpleGraph.disjoint_left.mp hHG u v hH hG
      have hnotCovered : ¬ (coveredGraph S.chosen).Adj u v := by
        intro hcovered
        exact (mem_sdiff.mp he).2 (mem_graphEdges_iff.mpr hcovered)
      have hleave : (leaveGraph S.chosen).Adj u v :=
        leaveGraph_adj.mpr ⟨hG.ne, hnotCovered⟩
      simpa [PairAlive, Sym2.toFinset_mk_eq] using
        (houtside u v hnotH hnotBoth hleave)

theorem hasPreliminaryEdgeSupply_of_outsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    {H G : SimpleGraph V} {X : Finset V} {S : GreedyStateOn V}
    {d : ℕ} (hHG : Disjoint H G)
    (houtside : OutsideLeavePairsAlive H X S)
    (hfloor : HasAvailablePairFloor d S) :
    HasPreliminaryEdgeSupply G X d S :=
  hasPreliminaryEdgeSupply_of_pairFloor_alive hfloor
    (availablePair_nonempty_of_outsideLeavePairsAlive hHG houtside)

end

end Erdos207
