/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailabilityLowerTrajectory
import ErdosProblems.Erdos207.AvailabilityUpperTrajectory
import ErdosProblems.Erdos207.OuterOnlyResidualDegree

/-!
# Exact availability clock for an outer-only phase

Every chosen and available triple in the initial phase is supported on the
internal outer graph.  Its uncovered edge set therefore supplies both sides
of the total-availability estimate.  Packinghood removes exactly three such
edges at each step, so the lower and upper schedules use one common clock.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The internal-outer graph edges not yet covered by the chosen packing. -/
def outerOnlyLiveEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V) :
    Finset (Sym2 V) :=
  greedyUncoveredEdges (internalOuterEdges G U) S

/-- The complement of a finite graph consists of the complete-graph edges
outside that graph. -/
lemma graphEdges_compl_eq_complete_sdiff
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    graphEdges Gᶜ =
      graphEdges (SimpleGraph.completeGraph V) \ graphEdges G := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp [mem_graphEdges_iff, SimpleGraph.compl_adj]

/-- Complementary simple graphs partition all two-element vertex pairs. -/
lemma card_graphEdges_compl_eq_choose_sub
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    (graphEdges Gᶜ).card =
      Nat.choose (Fintype.card V) 2 - (graphEdges G).card := by
  rw [graphEdges_compl_eq_complete_sdiff,
    card_sdiff_of_subset]
  · rw [graphEdges_eq_edgeFinset,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  · intro e he
    rw [mem_graphEdges_completeGraph_iff_not_isDiag]
    exact G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he)

/-- A packing covers exactly three graph edges per chosen triple. -/
lemma card_graphEdges_coveredGraph_of_isPackingOn
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : TripleSystemOn V} (hpacking : IsPackingOn P) :
    (graphEdges (coveredGraph P)).card = 3 * P.card := by
  rw [graphEdges_eq_edgeFinset, coveredGraph_edgeFinset_eq_biUnion,
    card_biUnion_tripleEdgeFinset_of_isPackingOn hpacking]

/-- The chosen family in an outer-only invariant consists of outer-only
triangles of the ambient graph. -/
lemma absorberGreedyInvariant_chosen_outer_geometry
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V}
    (hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A) :
    graphEdges (coveredGraph S.chosen) ⊆ internalOuterEdges G U := by
  apply covered_edges_subset_internalOuterEdges htri
  · exact hAbs.2.1.1.trans (outerOnlyAvailable_subset U A)
  · intro T hT
    exact (mem_outerOnlyAvailable_iff.mp (hAbs.2.1.1 hT)).2

/-- Exact cardinality of the live internal-outer edge set. -/
lemma card_outerOnlyLiveEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V}
    (hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A) :
    (outerOnlyLiveEdges G U S).card =
      (internalOuterEdges G U).card - 3 * S.chosen.card := by
  rw [outerOnlyLiveEdges, greedyUncoveredEdges,
    card_sdiff_of_subset
      (absorberGreedyInvariant_chosen_outer_geometry hAbs htri),
    card_graphEdges_coveredGraph_of_isPackingOn hAbs.1.1]

/-- The clock written using the complement graph is exactly the internal
outer-edge clock. -/
lemma outerOnly_pairClock_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V} {i : ℕ}
    (hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A)
    (hcard : S.chosen.card = i) :
    Nat.choose (Fintype.card V) 2 - 3 * i -
        (graphEdges (internalOuterGraph G U)ᶜ).card =
      (outerOnlyLiveEdges G U S).card := by
  classical
  have hcovered := absorberGreedyInvariant_chosen_outer_geometry hAbs htri
  have hcoveredCard := card_graphEdges_coveredGraph_of_isPackingOn hAbs.1.1
  have hle : 3 * i ≤ (internalOuterEdges G U).card := by
    rw [← hcard, ← hcoveredCard]
    exact card_le_card hcovered
  rw [card_outerOnlyLiveEdges hAbs htri, hcard,
    card_graphEdges_compl_eq_choose_sub,
    graphEdges_internalOuterGraph]
  have htotal : (internalOuterEdges G U).card ≤
      Nat.choose (Fintype.card V) 2 := by
    rw [← graphEdges_internalOuterGraph G U, graphEdges_eq_edgeFinset]
    exact SimpleGraph.card_edgeFinset_le_card_choose_two
  omega

/-- Every edge of an available outer-only triple is one of the live
internal-outer edges. -/
lemma tripleEdgeFinset_subset_outerOnlyLiveEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V}
    (hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A)
    {T : TripleOn V} (hT : T ∈ S.available) :
    tripleEdgeFinset T ⊆ outerOnlyLiveEdges G U S := by
  intro e he
  have hoff : ¬ e.IsDiag := not_isDiag_of_mem_tripleEdgeFinset he
  have hne : e.out.1 ≠ e.out.2 := by
    intro h
    apply hoff
    rw [← e.out_eq, Sym2.mk_isDiag_iff]
    exact h
  have hpairSub : e.toFinset ⊆ T.1 :=
    (mem_tripleEdgeFinset_iff_toFinset_subset_of_not_isDiag e T hoff).mp he
  have hfstT : e.out.1 ∈ T.1 := hpairSub <|
    Sym2.mem_toFinset.mpr (Sym2.out_fst_mem e)
  have hsndT : e.out.2 ∈ T.1 := hpairSub <|
    Sym2.mem_toFinset.mpr (Sym2.out_snd_mem e)
  have hTout := mem_outerOnlyAvailable_iff.mp (hAbs.2.1.2 hT)
  have hG : G.Adj e.out.1 e.out.2 :=
    htri T hTout.1 e.out.1 hfstT e.out.2 hsndT hne
  have hfstOut : e.out.1 ∉ U := by
    intro hU
    exact Finset.disjoint_left.mp hTout.2 hfstT hU
  have hsndOut : e.out.2 ∉ U := by
    intro hU
    exact Finset.disjoint_left.mp hTout.2 hsndT hU
  have hinter : e ∈ internalOuterEdges G U :=
    mem_internalOuterEdges_iff.mpr
      ⟨mem_graphEdges_iff.mpr (e.out_eq ▸ hG), hfstOut, hsndOut⟩
  have hnotCovered : e ∉ graphEdges (coveredGraph S.chosen) := by
    intro hcovered
    have hcoveredAdj := graph_adj_out_of_mem_graphEdges hcovered
    obtain ⟨W, hW, hfstW, hsndW, _hneW⟩ :=
      coveredGraph_adj.mp hcoveredAdj
    have hlegal := hAbs.1.2.2 T hT
    have hTW : T = W := hlegal.2.1 e.out.1 e.out.2 hne T
      (mem_insert_self T S.chosen) hfstT hsndT W
      (mem_insert_of_mem hW) hfstW hsndW
    exact hlegal.1 (hTW ▸ hW)
  exact mem_sdiff.mpr ⟨hinter, hnotCovered⟩

/-- Double counting over the live internal-outer edges counts every
available triple exactly three times. -/
lemma sum_outerOnlyLiveEdges_card_greedyChoicesCoveringEdge_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V}
    (hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A) :
    ∑ e ∈ outerOnlyLiveEdges G U S,
        (greedyChoicesCoveringEdge S e).card = 3 * S.available.card := by
  rw [sum_card_greedyChoicesCoveringEdge_eq]
  calc
    (∑ T : S.available,
        ((outerOnlyLiveEdges G U S).filter fun e ↦
          e ∈ tripleEdgeFinset T.1).card) =
        ∑ _T : S.available, 3 := by
      apply sum_congr rfl
      intro T _hT
      have hsub := tripleEdgeFinset_subset_outerOnlyLiveEdges hAbs htri T.2
      have heq : (outerOnlyLiveEdges G U S).filter
          (fun e ↦ e ∈ tripleEdgeFinset T.1) = tripleEdgeFinset T.1 := by
        ext e
        simp only [mem_filter]
        constructor
        · exact fun h ↦ h.2
        · exact fun h ↦ ⟨hsub h, h⟩
      rw [heq, card_tripleEdgeFinset]
    _ = 3 * S.available.card := by simp [Nat.mul_comm]

/-- A pair cutoff gives the sharp upper availability bound on the common
outer-only edge clock. -/
theorem available_card_le_outerOnlyLiveEdges_mul_pairCutoff_div_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V} {u : ℕ}
    (hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A)
    (hpair : HasAvailablePairCutoff u S) :
    S.available.card ≤ (outerOnlyLiveEdges G U S).card * u / 3 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
  rw [Nat.mul_comm, ←
    sum_outerOnlyLiveEdges_card_greedyChoicesCoveringEdge_eq hAbs htri]
  calc
    (∑ e ∈ outerOnlyLiveEdges G U S,
        (greedyChoicesCoveringEdge S e).card) ≤
        ∑ _e ∈ outerOnlyLiveEdges G U S, u := by
      apply sum_le_sum
      intro e he
      have heInternal : e ∈ internalOuterEdges G U :=
        (mem_sdiff.mp he).1
      have hoff : ¬ e.IsDiag :=
        (by
          have heGraph := internalOuterEdges_subset_graphEdges G U heInternal
          exact G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp heGraph))
      rw [card_greedyChoicesCoveringEdge_eq_availablePair S e hoff]
      exact hpair e.toFinset
        (Sym2.card_toFinset_of_not_isDiag e hoff)
    _ = (outerOnlyLiveEdges G U S).card * u := by simp [Nat.mul_comm]

/-- Outside-pair survival gives the matching lower availability bound on
the same live edge set. -/
theorem outerOnlyLiveEdges_card_mul_pairFloor_div_three_le_available
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V} {d : ℕ}
    (_hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (houtside : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S)
    (hfloor : HasAvailablePairFloor d S) :
    (outerOnlyLiveEdges G U S).card * d / 3 ≤ S.available.card := by
  have hsupply : ∀ e ∈ outerOnlyLiveEdges G U S,
      d ≤ (greedyChoicesCoveringEdge S e).card := by
    simpa only [outerOnlyLiveEdges, outerGraphEdges_internalOuterGraph] using
      (outerEdgeSupply_of_outsideLeavePairsAlive
        (H := (internalOuterGraph G U)ᶜ) (G := internalOuterGraph G U)
        (X := U) (S := S) (d := d)
        (by simp [SimpleGraph.disjoint_left]) houtside hfloor)
  have hcover := card_mul_div_three_le_greedyCoveringChoices S
    (outerOnlyLiveEdges G U S) d hsupply
  calc
    (outerOnlyLiveEdges G U S).card * d / 3 ≤
        (greedyCoveringChoices S (outerOnlyLiveEdges G U S)).card := hcover
    _ ≤ (univ : Finset S.available).card :=
      card_le_card (subset_univ _)
    _ = S.available.card := by simp

/-- Clock-synchronized lower availability estimate. -/
theorem scheduled_available_floor_outerOnly_exact
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V} {i d D : ℕ}
    (hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A)
    (houtside : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S)
    (hcard : S.chosen.card = i)
    (hfloor : HasAvailablePairFloor d S)
    (hD : D ≤ (Nat.choose (Fintype.card V) 2 - 3 * i -
        (graphEdges (internalOuterGraph G U)ᶜ).card) * d / 3) :
    D ≤ S.available.card := by
  rw [outerOnly_pairClock_eq hAbs htri hcard] at hD
  exact hD.trans
    (outerOnlyLiveEdges_card_mul_pairFloor_div_three_le_available
      hAbs houtside hfloor)

/-- Clock-synchronized upper availability estimate. -/
theorem scheduled_available_ceiling_outerOnly_exact
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {A : TripleSystemOn V} {S : GreedyStateOn V} {i u M : ℕ}
    (hAbs : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S)
    (htri : ConsistsOfTriangles G A)
    (hcard : S.chosen.card = i)
    (hpair : HasAvailablePairCutoff u S)
    (hM : (Nat.choose (Fintype.card V) 2 - 3 * i -
        (graphEdges (internalOuterGraph G U)ᶜ).card) * u / 3 ≤ M) :
    S.available.card ≤ M := by
  rw [outerOnly_pairClock_eq hAbs htri hcard] at hM
  exact (available_card_le_outerOnlyLiveEdges_mul_pairCutoff_div_three
    hAbs htri hpair).trans hM

end

end Erdos207
