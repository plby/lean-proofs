/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterOnlyExactAvailability
import ErdosProblems.Erdos207.StoppedGreedyVertexStarConcentration

/-!
# Vertex-star selection rates in the outer-only process

At a fixed vertex, double counting the live incident pair stars counts each
available triangle through the vertex exactly twice.  Consequently a live
residual degree `R`, pair-star floor `d`, and total-availability ceiling `M`
give the one-step selection-rate lower bound `R d / (2 M)`.  This is the
local deterministic input for the stopped lower-tail estimate on selected
vertex stars.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- The live internal-outer edges are exactly the preliminary residual
internal edges of the currently selected family. -/
lemma outerOnlyLiveEdges_eq_preliminaryResidualInternalEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V) :
    outerOnlyLiveEdges G U S =
      preliminaryResidualInternalEdges G U S.chosen := by
  ext e
  simp only [outerOnlyLiveEdges, greedyUncoveredEdges,
    preliminaryResidualInternalEdges, preliminaryResidualOuterEdges,
    mem_sdiff, mem_inter]
  constructor
  · rintro ⟨heInternal, heNotCovered⟩
    exact ⟨heInternal,
      internalOuterEdges_subset_outerGraphEdges G U heInternal,
      heNotCovered⟩
  · rintro ⟨heInternal, _heOuter, heNotCovered⟩
    exact ⟨heInternal, heNotCovered⟩

/-- An endpoint of one of a triple's graph edges is a vertex of the triple. -/
lemma mem_triple_of_mem_edge_of_mem
    {V : Type*} [DecidableEq V] {T : TripleOn V} {e : Sym2 V} {v : V}
    (he : e ∈ tripleEdgeFinset T) (hv : v ∈ e) :
    v ∈ T.1 := by
  rw [← e.out_eq] at he hv
  have hxy := mk_mem_tripleEdgeFinset_iff.mp he
  rcases Sym2.mem_iff.mp hv with hv | hv
  · exact hv ▸ hxy.1
  · exact hv ▸ hxy.2.1

/-- At most two of the three edges of a triple are incident with a fixed
vertex. -/
lemma card_scheduledEdgesAt_tripleEdgeFinset_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : TripleOn V) (v : V) :
    (scheduledEdgesAt (tripleEdgeFinset T) v).card ≤ 2 := by
  let C : TripleSystemOn V := {T}
  have hedges : graphEdges (coveredGraph C) = tripleEdgeFinset T := by
    rw [graphEdges_eq_edgeFinset, coveredGraph_edgeFinset_eq_biUnion]
    simp [C]
  calc
    (scheduledEdgesAt (tripleEdgeFinset T) v).card =
        (scheduledEdgesAt (graphEdges (coveredGraph C)) v).card := by
      rw [hedges]
    _ = (coveredGraph C).degree v :=
      card_scheduledEdgesAt_graphEdges (coveredGraph C) v
    _ = 2 * (triplesThrough C v).card :=
      (isPackingOn_singleton T).coveredGraph_degree_eq_two_mul_triplesThrough v
    _ ≤ 2 * C.card := Nat.mul_le_mul_left 2
      (card_le_card (filter_subset _ _))
    _ = 2 := by simp [C]

/-- Local double counting: the sum of the available pair-star sizes over
the live edges incident with `v` is at most twice the available vertex-star
size. -/
theorem sum_liveIncident_card_greedyChoicesCoveringEdge_le_two_mul_star
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V}
    (hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A) (v : V) :
    ∑ e ∈ scheduledEdgesAt (outerOnlyLiveEdges G U S) v,
        (greedyChoicesCoveringEdge S e).card ≤
      2 * (availableTriplesThrough S v).card := by
  rw [sum_card_greedyChoicesCoveringEdge_eq]
  calc
    (∑ T : S.available,
        ((scheduledEdgesAt (outerOnlyLiveEdges G U S) v).filter
          fun e ↦ e ∈ tripleEdgeFinset T.1).card) ≤
        ∑ T : S.available, if v ∈ T.1.1 then 2 else 0 := by
      apply sum_le_sum
      intro T _hT
      by_cases hvT : v ∈ T.1.1
      · rw [if_pos hvT]
        apply (card_le_card ?_).trans
          (card_scheduledEdgesAt_tripleEdgeFinset_le_two T.1 v)
        intro e he
        have hdata := mem_filter.mp he
        exact mem_scheduledEdgesAt_iff.mpr
          ⟨hdata.2, (mem_scheduledEdgesAt_iff.mp hdata.1).2⟩
      · rw [if_neg hvT]
        have hempty :
            (scheduledEdgesAt (outerOnlyLiveEdges G U S) v).filter
                (fun e ↦ e ∈ tripleEdgeFinset T.1) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro e he
          have hdata := mem_filter.mp he
          exact hvT (mem_triple_of_mem_edge_of_mem hdata.2
            (mem_scheduledEdgesAt_iff.mp hdata.1).2)
        simp [hempty]
    _ = 2 * (∑ T : S.available,
        if v ∈ T.1.1 then (1 : ℕ) else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro T _hT
      split_ifs <;> simp
    _ = 2 * (availableTriplesThrough S v).card := by
      congr 1
      exact_mod_cast sum_available_vertex_indicator S v

/-- A residual degree and a live pair floor force a proportional number of
available choices through the vertex. -/
theorem residualDegree_mul_pairFloor_le_two_mul_availableVertexStar
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V} {R d : ℕ}
    (hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A)
    (houtside : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S)
    (hfloor : HasAvailablePairFloor d S) (v : V)
    (hdegree : R ≤ (scheduledEdgesAt
      (preliminaryResidualInternalEdges G U S.chosen) v).card) :
    R * d ≤ 2 * (availableTriplesThrough S v).card := by
  let B := scheduledEdgesAt (outerOnlyLiveEdges G U S) v
  have hBcard : R ≤ B.card := by
    simpa only [B, outerOnlyLiveEdges_eq_preliminaryResidualInternalEdges]
      using hdegree
  have hsupply : ∀ e ∈ B,
      d ≤ (greedyChoicesCoveringEdge S e).card := by
    intro e he
    have heLive : e ∈ outerOnlyLiveEdges G U S :=
      (mem_scheduledEdgesAt_iff.mp he).1
    have heInternal : e ∈ internalOuterEdges G U := (mem_sdiff.mp heLive).1
    have hoff : ¬ e.IsDiag := by
      have heGraph := internalOuterEdges_subset_graphEdges G U heInternal
      exact G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp heGraph)
    rw [card_greedyChoicesCoveringEdge_eq_availablePair S e hoff]
    apply hfloor e.toFinset (Sym2.card_toFinset_of_not_isDiag e hoff)
    have heOuterLive : e ∈ greedyUncoveredEdges
        (outerGraphEdges (internalOuterGraph G U) U) S := by
      simpa only [outerOnlyLiveEdges, outerGraphEdges_internalOuterGraph] using
        heLive
    simpa only using
      (availablePair_nonempty_of_outsideLeavePairsAlive_outer
        (H := (internalOuterGraph G U)ᶜ)
        (G := internalOuterGraph G U) (X := U) (S := S)
        (by simp [SimpleGraph.disjoint_left]) houtside e heOuterLive)
  calc
    R * d ≤ B.card * d := Nat.mul_le_mul_right d hBcard
    _ = ∑ _e ∈ B, d := by simp [mul_comm]
    _ ≤ ∑ e ∈ B, (greedyChoicesCoveringEdge S e).card := by
      apply sum_le_sum
      intro e he
      exact hsupply e he
    _ ≤ 2 * (availableTriplesThrough S v).card :=
      sum_liveIncident_card_greedyChoicesCoveringEdge_le_two_mul_star
        hAbs htri v

/-- Deterministic lower bound used for the probability that the next greedy
choice contains a vertex whose residual degree is still at least `R`. -/
def outerOnlyVertexSelectionRate
    (R : ℕ) (d M : ℕ → ℕ) (i : ℕ) : ℝ :=
  ((R * d i : ℕ) : ℝ) / (2 * (M i : ℕ))

lemma outerOnlyVertexSelectionRate_nonneg
    (R : ℕ) (d M : ℕ → ℕ) (i : ℕ) :
    0 ≤ outerOnlyVertexSelectionRate R d M i := by
  unfold outerOnlyVertexSelectionRate
  positivity

lemma outerOnlyVertexSelectionRate_le_one
    (R : ℕ) (d M : ℕ → ℕ) (i : ℕ)
    (hM : 0 < M i) (h : R * d i ≤ 2 * M i) :
    outerOnlyVertexSelectionRate R d M i ≤ 1 := by
  unfold outerOnlyVertexSelectionRate
  rw [div_le_one (by positivity)]
  exact_mod_cast h

/-- If the deterministic availability ceiling is at most the current clock
times the pair-degree floor, then the vertex-selection rate dominates the
reciprocal-clock rate. -/
lemma reciprocalClockRate_le_outerOnlyVertexSelectionRate
    (R : ℕ) (d M : ℕ → ℕ) (i E : ℕ)
    (hE : 0 < E) (hM : 0 < M i) (hME : M i ≤ E * d i) :
    (R : ℝ) / (2 * E) ≤ outerOnlyVertexSelectionRate R d M i := by
  have hEreal : (0 : ℝ) < 2 * E := by positivity
  have hMreal : (0 : ℝ) < 2 * (M i) := by positivity
  unfold outerOnlyVertexSelectionRate
  rw [div_le_div_iff₀ hEreal hMreal]
  exact_mod_cast (by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_left (2 * R) hME)

theorem outerOnlyVertexSelectionRate_le_available_ratio
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V} {R d M : ℕ}
    (hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A)
    (houtside : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S)
    (hfloor : HasAvailablePairFloor d S) (v : V)
    (hdegree : R ≤ (scheduledEdgesAt
      (preliminaryResidualInternalEdges G U S.chosen) v).card)
    (havailable : S.available.Nonempty) (hMpos : 0 < M)
    (hM : S.available.card ≤ M) :
    ((R * d : ℕ) : ℝ) / (2 * (M : ℕ)) ≤
      ((availableTriplesThrough S v).card : ℝ) /
        (S.available.card : ℝ) := by
  have hsupply := residualDegree_mul_pairFloor_le_two_mul_availableVertexStar
    hAbs htri houtside hfloor v hdegree
  have hcardPos : 0 < S.available.card := card_pos.mpr havailable
  rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hcardPos)]
  exact_mod_cast (calc
    R * d * S.available.card ≤
        (2 * (availableTriplesThrough S v).card) * S.available.card :=
      Nat.mul_le_mul_right S.available.card hsupply
    _ ≤ (2 * (availableTriplesThrough S v).card) * M :=
      Nat.mul_le_mul_left (2 * (availableTriplesThrough S v).card) hM
    _ = (availableTriplesThrough S v).card * (2 * M) := by ring)

/-- Enlarging the selected family can only shrink the preliminary residual
internal edge family. -/
lemma preliminaryResidualInternalEdges_antitone
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V)
    {P Q : TripleSystemOn V} (hPQ : P ⊆ Q) :
    preliminaryResidualInternalEdges G U Q ⊆
      preliminaryResidualInternalEdges G U P := by
  intro e he
  have hdata := mem_inter.mp he
  have hres := mem_sdiff.mp hdata.2
  apply mem_inter.mpr
  refine ⟨hdata.1, mem_sdiff.mpr ⟨hres.1, ?_⟩⟩
  intro heCoveredP
  have heEdgeP := mem_graphEdges_iff.mp heCoveredP
  exact hres.2 (mem_graphEdges_iff.mpr
    (SimpleGraph.edgeSet_mono (coveredGraph_mono hPQ) heEdgeP))

/-- Residual degree at a fixed vertex is antitone in the selected family. -/
lemma card_scheduled_preliminaryResidualInternalEdges_antitone
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (v : V)
    {P Q : TripleSystemOn V} (hPQ : P ⊆ Q) :
    (scheduledEdgesAt (preliminaryResidualInternalEdges G U Q) v).card ≤
      (scheduledEdgesAt (preliminaryResidualInternalEdges G U P) v).card := by
  apply card_le_card
  intro e he
  have hdata := mem_scheduledEdgesAt_iff.mp he
  exact mem_scheduledEdgesAt_iff.mpr
    ⟨preliminaryResidualInternalEdges_antitone G U hPQ hdata.1, hdata.2⟩

end

end Erdos207
