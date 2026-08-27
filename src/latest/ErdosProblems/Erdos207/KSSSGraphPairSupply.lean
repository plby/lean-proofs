/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSWorkingGraphSupply
import ErdosProblems.Erdos207.RegularizationGraphEncoding

/-! # Pair supply for the actual graph used in a recursive stage -/

namespace Erdos207

open Finset

noncomputable section

theorem graphEdge_toFinset_mem_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : GreedyStateOn V) (e : Sym2 V)
    (he : e ∈ graphEdges G) (huncovered : e ∉ (coveredGraph S.chosen).edgeSet) :
    e.toFinset ∈ ksssResidualPairs (graphPairFamily G) S := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hadj : G.Adj u v := mem_graphEdges_iff.mp he
    have hinit := (mem_graphPairFamily_toFinset_iff G s(u, v)).mpr he
    have hpair : PairUncovered {u, v} S :=
      (pairUncovered_pair_iff_not_covered_adj S hadj.ne).mpr huncovered
    simpa only [ksssResidualPairs, mem_sdiff, Sym2.toFinset_mk_eq, PairUncovered] using And.intro hinit hpair

theorem KSSSOnTrajectories.graph_pair_floor
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {G : SimpleGraph V}
    {a : ℕ → ℝ} {E A scale time : ℝ} {B : ℕ}
    (h : KSSSOnTrajectories F S q (ksssResidualPairs (graphPairFamily G) S) a E A scale B time)
    (e : Sym2 V) (he : e ∈ graphEdges G) (huncovered : e ∉ (coveredGraph S.chosen).edgeSet) :
    ksssRoundedPairFloor q a E A scale B time ≤ (greedyChoicesCoveringEdge S e).card := by
  have hpair := h.1 e.toFinset (graphEdge_toFinset_mem_residual G S e he huncovered)
  have hlower : ksssPairTrajectory (ksssOrders q) a E A time - ksssErrorEnvelope E scale B time ≤
      ((availableTrianglesContainingPair S e.toFinset).card : ℝ) := by
    have hlo := (abs_le.mp hpair).1
    linarith only [hlo]
  rw [card_greedyChoicesCoveringEdge_eq_availablePair S e
    (G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))]
  simpa only [ksssRoundedPairFloor, Nat.floor_natCast] using Nat.floor_mono hlower

end

end Erdos207
