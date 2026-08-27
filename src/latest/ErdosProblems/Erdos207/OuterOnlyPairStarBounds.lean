/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedPairAlive
import ErdosProblems.Erdos207.PairAggregateTwoAwayAbsorberBound
import ErdosProblems.Erdos207.TimedStoppedTotalTwoAway
import ErdosProblems.Erdos207.TimedSharpScheduledAggregatePairBand

/-!
# Quantitative initial pair stars for the outer-only phase

Iteration typicality counts canonical third vertices through each graph edge.
After removing the next vortex level and the two displayed endpoints, those
vertices inject into the corresponding pair star of the outer-only initial
state.  This is the quantitative strengthening of the nonemptiness argument
in `OuterOnlyPreliminaryGeometry` needed by the sharp scheduled phase.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Completely outside extension candidates inject into the corresponding
pair star of the canonical outer-only initial state. -/
lemma card_outerExtensionCandidates_le_outerOnly_pairStar
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {Uouter U : Finset V} {u v : V}
    (huv : u ≠ v) (hu : u ∉ U) (hv : v ∉ U)
    (hInv : GreedyInvariant F (relativePreliminaryInitialState ∅ A)) :
    (outerExtensionCandidates A Uouter U u v).card ≤
      (availableTrianglesContainingPair
        (absorberGreedyInitialState F (outerOnlyAvailable U A))
        {u, v}).card := by
  let C := outerExtensionCandidates A Uouter U u v
  let e : {w // w ∈ C} ↪ ThirdVertex u v :=
    { toFun := fun w =>
        ⟨w.1,
          (mem_outerExtensionCandidates_iff.mp w.2).2.2.1,
          (mem_outerExtensionCandidates_iff.mp w.2).2.2.2⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : ThirdVertex u v => z.1) hxy }
  let C' : Finset (ThirdVertex u v) := C.attach.map e
  let f : ThirdVertex u v ↪ TripleOn V :=
    ⟨thirdVertexTriple huv, thirdVertexTriple_injective huv⟩
  have hsub : C'.map f ⊆
      availableTrianglesContainingPair
        (absorberGreedyInitialState F (outerOnlyAvailable U A)) {u, v} := by
    intro T hT
    obtain ⟨w, hwC', rfl⟩ := mem_map.mp hT
    obtain ⟨x, hxC, hw⟩ := mem_map.mp hwC'
    subst w
    have hxdata := mem_outerExtensionCandidates_iff.mp x.2
    have hTA : thirdVertexTriple huv (e x) ∈ A := by
      exact iterationExtensionVertices_edge_thirdVertexTriple_mem_of_ne
        huv hxdata.2.2.1.symm hxdata.2.2.2.symm hxdata.1
    have hTdisj : Disjoint (thirdVertexTriple huv (e x)).1 U := by
      rw [Finset.disjoint_left]
      intro z hzT hzU
      simp only [thirdVertexTriple, tripleOfThree, mem_insert,
        mem_singleton] at hzT
      rcases hzT with rfl | rfl | rfl
      · exact hu hzU
      · exact hv hzU
      · exact hxdata.2.1 hzU
    rw [absorberGreedyInitialState_outerOnly_eq_relative U hInv]
    apply mem_availableTrianglesContainingPair_iff.mpr
    refine ⟨mem_outerOnlyAvailable_iff.mpr ⟨hTA, hTdisj⟩, ?_⟩
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact left_mem_thirdVertexTriple huv (e x)
    · have hzv : z = v := by simpa using hz
      subst z
      exact right_mem_thirdVertexTriple huv (e x)
  calc
    C.card = (C'.map f).card := by simp [C']
    _ ≤ (availableTrianglesContainingPair
        (absorberGreedyInitialState F (outerOnlyAvailable U A))
        {u, v}).card := card_le_card hsub

/-- Endpoint-oriented form of the iteration-typical lower bound.  Keeping
the displayed endpoints avoids any orientation choice for `Sym2.out`. -/
lemma IsIterationTypical.outerExtensionCandidates_card_gt_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h) (m : ℕ)
    (hgap : ((((W.U i.succ).card + 2 + m : ℕ) : ℝ≥0)) <
      (1 - xi) * (p ^ 2 * eta * (W.U i.castSucc).card))
    {u v : V} (huv : u ≠ v) (huvG : G.Adj u v) :
    m < (outerExtensionCandidates A (W.U i.castSucc)
      (W.U i.succ) u v).card := by
  have hsupp := hGsupp huvG
  have hwindow := htyp.2 i hstage i.castSucc (Or.inl rfl)
    (SimpleGraph.edge u v)
    (SimpleGraph.edge_le_iff G |>.mpr (Or.inr huvG))
    (edge_graphSupportedOn hsupp.1 hsupp.2) (by
      rw [graphSupportFinset_edge huv, card_pair huv]
      exact hh)
  rw [graphSupportFinset_edge huv, card_pair huv,
    graphEdges_edge huv, card_singleton, pow_one] at hwindow
  have hcard : (W.U i.succ).card + 2 + m <
      (iterationExtensionVertices A (SimpleGraph.edge u v)
        (W.U i.castSucc)).card := by
    exact_mod_cast hgap.trans_le hwindow.1
  exact card_outerExtensionCandidates_gt m hcard

/-- A uniform lower extension window gives a uniform initial pair-star
floor on the outer-only family.  Only nonempty pair stars are relevant; a
triangle witnessing nonemptiness shows that the displayed pair is a graph
edge with both endpoints outside the inner level. -/
theorem IsIterationTypical.hasAvailablePairFloor_outerOnly
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {A : TripleSystemOn V} {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h) (m : ℕ)
    (hgap : ((((W.U i.succ).card + 2 + m : ℕ) : ℝ≥0)) <
      (1 - xi) * (p ^ 2 * eta * (W.U i.castSucc).card))
    (hInv : GreedyInvariant F (relativePreliminaryInitialState ∅ A)) :
    HasAvailablePairFloor (m + 1)
      (absorberGreedyInitialState F
        (outerOnlyAvailable (W.U i.succ) A)) := by
  intro P hPcard hPnonempty
  obtain ⟨T, hTstar⟩ := hPnonempty
  have hTdata := mem_availableTrianglesContainingPair_iff.mp hTstar
  rw [absorberGreedyInitialState_outerOnly_eq_relative
    (W.U i.succ) hInv] at hTdata
  have hTout := mem_outerOnlyAvailable_iff.mp hTdata.1
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hPcard
  have huT : u ∈ T.1 := hTdata.2 (by simp)
  have hvT : v ∈ T.1 := hTdata.2 (by simp)
  have huout : u ∉ W.U i.succ := by
    intro huU
    exact Finset.disjoint_left.mp hTout.2 huT huU
  have hvout : v ∉ W.U i.succ := by
    intro hvU
    exact Finset.disjoint_left.mp hTout.2 hvT hvU
  have huvG : G.Adj u v := htri T hTout.1 u huT v hvT huv
  have heGraph : s(u, v) ∈ graphEdges G := mem_graphEdges_iff.mpr huvG
  have hcand : m <
      (outerExtensionCandidates A (W.U i.castSucc) (W.U i.succ)
        u v).card := by
    exact htyp.outerExtensionCandidates_card_gt_edge i hstage hGsupp hh m
      hgap huv huvG
  have hstar :
      (outerExtensionCandidates A (W.U i.castSucc) (W.U i.succ)
          u v).card ≤
        (availableTrianglesContainingPair
          (absorberGreedyInitialState F
            (outerOnlyAvailable (W.U i.succ) A)) {u, v}).card := by
    exact card_outerExtensionCandidates_le_outerOnly_pairStar
      huv huout hvout hInv
  omega

/-- At the empty packing, a selected-count is exactly the extension weight
above the empty root, independently of the point weights. -/
lemma selectedCount_empty_le_extensionWeight_empty
    {W I : Type*} [DecidableEq W] [Fintype I]
    (configurations : I → Finset W) (pi : W → ℝ≥0) :
    selectedCount configurations ∅ ≤
      extensionWeight configurations pi ∅ := by
  classical
  unfold selectedCount extensionWeight
  apply sum_le_sum
  intro z _hz
  by_cases hempty : configurations z = ∅
  · simp [hempty, setWeight]
  · simp [hempty]

/-- The ambient-independent pair-local extension coefficient is already a
deterministic pair-two-away cutoff at an empty initial packing. -/
theorem hasPairTwoAwayCutoff_absorber_of_chosen_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {S : GreedyStateOn V}
    (hchosen : S.chosen = ∅) :
    HasPairTwoAwayCutoff
      (absorberErdosForbiddenConfigurationsOn q B)
      (pairTwoAwayThreatExtensionCoefficient q B) S := by
  intro U hU P hPcard hnotPU
  let P' : PairOn V := ⟨P, hPcard⟩
  have hcount :
      ((availableTrianglesContainingPair S P ∩
        nonPairTwoAwayForbiddenTriangles
          (absorberErdosForbiddenConfigurationsOn q B) S.chosen U).card :
          ℝ≥0) ≤
        selectedCount
          (fun z : PairTwoAwayThreatWitness V
              (absorberErdosForbiddenConfigurationsOn q B) U P' ↦
            pairTwoAwayThreatRemainder z) S.chosen := by
    calc
      ((availableTrianglesContainingPair S P ∩
          nonPairTwoAwayForbiddenTriangles
            (absorberErdosForbiddenConfigurationsOn q B) S.chosen U).card :
            ℝ≥0) ≤
          ((activePairTwoAwayThreatWitnesses
            (absorberErdosForbiddenConfigurationsOn q B) S.chosen U P').card :
              ℝ≥0) := by
        exact_mod_cast available_pair_nonPairTwoAway_card_le_witnesses
          (absorberErdosForbiddenConfigurationsOn q B) S U P'
      _ = selectedCount
          (fun z : PairTwoAwayThreatWitness V
              (absorberErdosForbiddenConfigurationsOn q B) U P' ↦
            pairTwoAwayThreatRemainder z) S.chosen := by
        symm
        exact selectedCount_pairTwoAwayThreatRemainder
          (absorberErdosForbiddenConfigurationsOn q B) S.chosen U P'
  have hext : selectedCount
        (fun z : PairTwoAwayThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) U P' ↦
          pairTwoAwayThreatRemainder z) S.chosen ≤
      (pairTwoAwayThreatExtensionCoefficient q B : ℕ) := by
    rw [hchosen]
    exact (selectedCount_empty_le_extensionWeight_empty _ _).trans
      (absorberPairTwoAwayThreatRemainder_hasExtensionBound ∅)
  exact_mod_cast hcount.trans hext

/-- The global two-away extension coefficient is a deterministic cutoff at
an empty initial packing. -/
theorem hasTwoAwayCutoff_absorber_of_chosen_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {S : GreedyStateOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hchosen : S.chosen = ∅) :
    HasTwoAwayCutoff
      (absorberErdosForbiddenConfigurationsOn q B)
      (twoAwayThreatExtensionCoefficient q M H X B) S := by
  intro U hU
  have hcount := twoAwayForbidden_count_le_selectedCount
    (absorberErdosForbiddenConfigurationsOn q B) S.chosen U
  have hext : selectedCount
        (fun z : TwoAwayThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) U ↦
          twoAwayThreatRemainder z) S.chosen ≤
      (twoAwayThreatExtensionCoefficient q M H X B : ℕ) := by
    rw [hchosen]
    exact (selectedCount_empty_le_extensionWeight_empty _ _).trans
      (absorberTwoAwayThreatRemainder_hasExtensionBound hA2 ∅)
  exact_mod_cast hcount.trans hext

/-- The aggregate pair-star extension coefficient is likewise a
deterministic incidence cutoff at an empty initial packing. -/
theorem hasPairStarTwoAwayIncidenceCutoff_absorber_of_chosen_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {S : GreedyStateOn V}
    (hchosen : S.chosen = ∅) :
    HasPairStarTwoAwayIncidenceCutoff
      (absorberErdosForbiddenConfigurationsOn q B)
      (aggregatePairTwoAwayThreatExtensionCoefficient q B *
        (Fintype.card V + 1) ^ 2) S := by
  intro P hPcard
  let P' : PairOn V := ⟨P, hPcard⟩
  have hcount := pairStarAvailableTwoAwayIncidences_le_selectedCount
    (absorberErdosForbiddenConfigurationsOn q B) S P'
  have hext : selectedCount
        (fun z : AggregatePairTwoAwayThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) P' ↦
          aggregatePairTwoAwayThreatRemainder z) S.chosen ≤
      ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ 2) := by
    rw [hchosen]
    exact (selectedCount_empty_le_extensionWeight_empty _ _).trans
      (absorberAggregatePairTwoAwayThreatRemainder_hasExtensionBound ∅)
  exact_mod_cast hcount.trans hext

/-- A global two-away cutoff bounds the total ordered available incidence
count by the number of ambient triples times that cutoff. -/
lemma totalAvailableTwoAwayIncidences_le_card_mul_of_cutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {K : ℕ}
    (hcut : HasTwoAwayCutoff F K S) :
    totalAvailableTwoAwayIncidences F S ≤
      Fintype.card (TripleOn V) * K := by
  calc
    totalAvailableTwoAwayIncidences F S =
        ∑ U : S.available,
          (availableTwoAwayForbiddenTriangles F S U.1).card := rfl
    _ ≤ ∑ _U : S.available, K := by
      apply sum_le_sum
      intro U _hU
      exact (card_le_card inter_subset_right).trans (hcut U.1 U.2)
    _ = S.available.card * K := by simp
    _ ≤ Fintype.card (TripleOn V) * K := by
      gcongr
      exact card_le_univ S.available

/-- All non-scalar clauses of the sharp scheduled active predicate hold in
the canonical empty outer-only state.  The remaining hypotheses are exactly
the five elementary comparisons between the chosen schedules and the actual
initial cardinalities. -/
theorem timedSharpScheduledAggregatePairBandActive_outerOnly_initial
    {V : Type*} [Fintype V] [DecidableEq V]
    {q Mloc m Dcut : ℕ} {H : SimpleGraph V} {X U : Finset V}
    {B A : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q Mloc H X B)
    (hfloor : HasAvailablePairFloor (m + 1)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (D d Mschedule u : ℕ → ℕ)
    (hDcutPos : 0 < Dcut)
    (hDcut : Dcut ≤
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)).available.card)
    (hD : D 0 ≤
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)).available.card)
    (hd : d 0 ≤ m + 1)
    (hM : Fintype.card (TripleOn V) ≤ Mschedule 0)
    (hu : Fintype.card V ≤ u 0) :
    timedSharpScheduledAggregatePairBandActive
      (absorberErdosForbiddenConfigurationsOn q B)
      (pairTwoAwayThreatExtensionCoefficient q B)
      (twoAwayThreatExtensionCoefficient q Mloc H X B)
      (aggregatePairTwoAwayThreatExtensionCoefficient q B *
        (Fintype.card V + 1) ^ 2)
      (Fintype.card V) (m + 1)
      (Fintype.card (TripleOn V) *
        twoAwayThreatExtensionCoefficient q Mloc H X B)
      Dcut D d Mschedule u 0
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F (outerOnlyAvailable U A)
  have hchosen : S₀.chosen = ∅ := by
    simp [S₀, absorberGreedyInitialState]
  have hglobal : HasTwoAwayCutoff F
      (twoAwayThreatExtensionCoefficient q Mloc H X B) S₀ := by
    exact hasTwoAwayCutoff_absorber_of_chosen_empty hA2 hchosen
  have htotal : totalAvailableTwoAwayIncidences F S₀ ≤
      Fintype.card (TripleOn V) *
        twoAwayThreatExtensionCoefficient q Mloc H X B :=
    totalAvailableTwoAwayIncidences_le_card_mul_of_cutoff hglobal
  have hnonempty : S₀.available.Nonempty := by
    rw [← card_pos]
    exact hDcutPos.trans_le (by simpa only [S₀, F] using hDcut)
  unfold timedSharpScheduledAggregatePairBandActive
  refine ⟨?_, ?_⟩
  · unfold timedFullyScheduledAggregatePairBandActive
    refine ⟨?_, (card_le_univ S₀.available).trans hM⟩
    unfold timedScheduledAggregatePairBandActive
    refine ⟨?_, by simpa only [S₀, F] using hD, ?_⟩
    · unfold timedAggregateAveragePairBandActive
      refine ⟨?_,
        hasPairStarTwoAwayIncidenceCutoff_absorber_of_chosen_empty hchosen⟩
      unfold timedAveragePairBandActive
      refine ⟨?_, htotal, by simpa only [S₀, F] using hDcut⟩
      exact ⟨hnonempty,
        initial_hasAvailablePairCutoff_card F (outerOnlyAvailable U A),
        hasPairTwoAwayCutoff_absorber_of_chosen_empty hchosen,
        hglobal, by simpa only [S₀, F] using hfloor⟩
    · exact fun P hPcard hPnonempty ↦
        hd.trans (hfloor P hPcard hPnonempty)
  · intro P hPcard
    exact (initial_hasAvailablePairCutoff_card F
      (outerOnlyAvailable U A) P hPcard).trans hu

/-- Monotone-cutoff version of the preceding initial-state constructor. -/
theorem timedSharpScheduledAggregatePairBandActive_outerOnly_initial_of_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {q Mloc m Kpair Kglobal Kinc Delta delta I Dcut : ℕ}
    {H : SimpleGraph V} {X U : Finset V} {B A : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q Mloc H X B)
    (hfloor : HasAvailablePairFloor (m + 1)
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)))
    (hKpair : pairTwoAwayThreatExtensionCoefficient q B ≤ Kpair)
    (hKglobal : twoAwayThreatExtensionCoefficient q Mloc H X B ≤ Kglobal)
    (hKinc : aggregatePairTwoAwayThreatExtensionCoefficient q B *
      (Fintype.card V + 1) ^ 2 ≤ Kinc)
    (hDelta : Fintype.card V ≤ Delta) (hdelta : delta ≤ m + 1)
    (hI : Fintype.card (TripleOn V) *
      twoAwayThreatExtensionCoefficient q Mloc H X B ≤ I)
    (D d Mschedule u : ℕ → ℕ)
    (hDcutPos : 0 < Dcut)
    (hDcut : Dcut ≤
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)).available.card)
    (hD : D 0 ≤
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)).available.card)
    (hd : d 0 ≤ m + 1)
    (hM : Fintype.card (TripleOn V) ≤ Mschedule 0)
    (hu : Fintype.card V ≤ u 0) :
    timedSharpScheduledAggregatePairBandActive
      (absorberErdosForbiddenConfigurationsOn q B)
      Kpair Kglobal Kinc Delta delta I Dcut D d Mschedule u 0
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outerOnlyAvailable U A)) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F (outerOnlyAvailable U A)
  have hchosen : S₀.chosen = ∅ := by
    simp [S₀, absorberGreedyInitialState]
  have hglobal₀ : HasTwoAwayCutoff F
      (twoAwayThreatExtensionCoefficient q Mloc H X B) S₀ :=
    hasTwoAwayCutoff_absorber_of_chosen_empty hA2 hchosen
  have hglobal : HasTwoAwayCutoff F Kglobal S₀ := by
    intro T hT
    exact (hglobal₀ T hT).trans hKglobal
  have htotal : totalAvailableTwoAwayIncidences F S₀ ≤ I :=
    (totalAvailableTwoAwayIncidences_le_card_mul_of_cutoff
      hglobal₀).trans hI
  have hnonempty : S₀.available.Nonempty := by
    rw [← card_pos]
    exact hDcutPos.trans_le (by simpa only [S₀, F] using hDcut)
  unfold timedSharpScheduledAggregatePairBandActive
  refine ⟨?_, ?_⟩
  · unfold timedFullyScheduledAggregatePairBandActive
    refine ⟨?_, (card_le_univ S₀.available).trans hM⟩
    unfold timedScheduledAggregatePairBandActive
    refine ⟨?_, by simpa only [S₀, F] using hD, ?_⟩
    · unfold timedAggregateAveragePairBandActive
      refine ⟨?_, ?_⟩
      · unfold timedAveragePairBandActive
        refine ⟨?_, htotal, by simpa only [S₀, F] using hDcut⟩
        refine ⟨hnonempty, ?_, ?_, hglobal, ?_⟩
        · intro P hPcard
          exact (initial_hasAvailablePairCutoff_card F
            (outerOnlyAvailable U A) P hPcard).trans hDelta
        · intro T hT P hPcard hnot
          exact (hasPairTwoAwayCutoff_absorber_of_chosen_empty hchosen
            T hT P hPcard hnot).trans hKpair
        · intro P hPcard hPnonempty
          exact hdelta.trans (hfloor P hPcard hPnonempty)
      · intro P hPcard
        exact (hasPairStarTwoAwayIncidenceCutoff_absorber_of_chosen_empty
          hchosen P hPcard).trans hKinc
    · exact fun P hPcard hPnonempty ↦
        hd.trans (hfloor P hPcard hPnonempty)
  · intro P hPcard
    exact (initial_hasAvailablePairCutoff_card F
      (outerOnlyAvailable U A) P hPcard).trans hu

end

end Erdos207
