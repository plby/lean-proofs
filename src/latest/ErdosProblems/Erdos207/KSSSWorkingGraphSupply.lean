/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedGraphInitialLaw
import ErdosProblems.Erdos207.UncoveredNeighborGraph
import ErdosProblems.Erdos207.KSSSPatternSelectors

/-! # Actual working-graph supply and rounded schedules from the coupled event -/

namespace Erdos207

open Finset

noncomputable section

theorem workingGraphEdge_toFinset_mem_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : GreedyStateOn V) (e : Sym2 V)
    (he : e ∈ graphEdges (graphDifference (SimpleGraph.completeGraph V) H))
    (huncovered : e ∉ (coveredGraph S.chosen).edgeSet) :
    e.toFinset ∈ ksssResidualPairs (initialResidualPairs H) S := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hadj : (graphDifference (SimpleGraph.completeGraph V) H).Adj u v := mem_graphEdges_iff.mp he
    have hinit : ({u, v} : Finset V) ∈ initialResidualPairs H :=
      (pair_mem_initialResidualPairs_iff H u v).mpr ⟨hadj.1, hadj.2.2⟩
    have hpair : PairUncovered {u, v} S :=
      (pairUncovered_pair_iff_not_covered_adj S hadj.1).mpr huncovered
    simpa only [ksssResidualPairs, mem_sdiff, Sym2.toFinset_mk_eq, PairUncovered] using And.intro hinit hpair

theorem initialAvailable_edges_in_workingGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (bank : TripleSystemOn V)
    {T : TripleOn V}
    (hT : T ∈ (absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank)
      (outsideAvailableTriangles H bank)).available) :
    tripleEdgeFinset T ⊆ graphEdges (graphDifference (SimpleGraph.completeGraph V) H) := by
  have havoid := (mem_outsideAvailableTriangles_iff.mp (mem_legalAvailable_iff.mp hT).1).2
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    obtain ⟨hu, hv, huv⟩ := mk_mem_tripleEdgeFinset_iff.mp he
    exact mem_graphEdges_iff.mpr ⟨huv, huv, havoid u hu v hv huv⟩

def ksssRoundedPairFloor (q : ℕ) (a : ℕ → ℝ) (E A scale : ℝ) (B : ℕ) (time : ℝ) : ℕ :=
  ⌊ksssPairTrajectory (ksssOrders q) a E A time - ksssErrorEnvelope E scale B time⌋₊

def ksssRoundedAvailabilityFloor (q : ℕ) (a : ℕ → ℝ) (E A scale : ℝ) (B : ℕ) (time : ℝ) : ℕ :=
  ⌊E * ksssEdgeDensity E time *
    (ksssPairTrajectory (ksssOrders q) a E A time - ksssErrorEnvelope E scale B time) / 3⌋₊

def ksssRoundedAvailabilityCeil (q : ℕ) (a : ℕ → ℝ) (E A scale : ℝ) (B : ℕ) (time : ℝ) : ℕ :=
  ⌈E * ksssEdgeDensity E time *
    (ksssPairTrajectory (ksssOrders q) a E A time + ksssErrorEnvelope E scale B time) / 3⌉₊

theorem KSSSOnTrajectories.working_graph_pair_floor
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {H : SimpleGraph V}
    {a : ℕ → ℝ} {E A scale time : ℝ} {B : ℕ}
    (h : KSSSOnTrajectories F S q (ksssResidualPairs (initialResidualPairs H) S) a E A scale B time)
    (e : Sym2 V) (he : e ∈ graphEdges (graphDifference (SimpleGraph.completeGraph V) H))
    (huncovered : e ∉ (coveredGraph S.chosen).edgeSet) :
    ksssRoundedPairFloor q a E A scale B time ≤ (greedyChoicesCoveringEdge S e).card := by
  have hpair := h.1 e.toFinset (workingGraphEdge_toFinset_mem_residual H S e he huncovered)
  have hlower : ksssPairTrajectory (ksssOrders q) a E A time - ksssErrorEnvelope E scale B time ≤
      ((availableTrianglesContainingPair S e.toFinset).card : ℝ) := by
    have hlo := (abs_le.mp hpair).1
    linarith only [hlo]
  rw [card_greedyChoicesCoveringEdge_eq_availablePair S e
    ((graphDifference (SimpleGraph.completeGraph V) H).not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))]
  simpa only [ksssRoundedPairFloor, Nat.floor_natCast] using Nat.floor_mono hlower

theorem KSSSOnTrajectories.rounded_availability_schedule
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {Q₀ : Finset (Finset V)}
    {a : ℕ → ℝ} {E A scale time : ℝ} {B : ℕ}
    (h : KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A scale B time)
    (hgeometry : KSSSResidualGeometry Q₀ S E time) :
    ksssRoundedAvailabilityFloor q a E A scale B time ≤ S.available.card ∧
      S.available.card ≤ ksssRoundedAvailabilityCeil q a E A scale B time := by
  have hglobal := h.availability_error hgeometry.pair_card hgeometry.cover
  rw [hgeometry.count] at hglobal
  have hbounds := abs_le.mp hglobal
  have hlo : E * ksssEdgeDensity E time *
      (ksssPairTrajectory (ksssOrders q) a E A time - ksssErrorEnvelope E scale B time) / 3 ≤
      (S.available.card : ℝ) := by nlinarith only [hbounds.1]
  have hhi : (S.available.card : ℝ) ≤ E * ksssEdgeDensity E time *
      (ksssPairTrajectory (ksssOrders q) a E A time + ksssErrorEnvelope E scale B time) / 3 := by
    nlinarith only [hbounds.2]
  exact ⟨by simpa only [ksssRoundedAvailabilityFloor, Nat.floor_natCast] using Nat.floor_mono hlo,
    by simpa only [ksssRoundedAvailabilityCeil, Nat.ceil_natCast] using Nat.ceil_mono hhi⟩

end

end Erdos207
