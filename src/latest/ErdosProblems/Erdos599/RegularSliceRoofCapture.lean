/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HeightRoofBridge
import ErdosProblems.Erdos599.RegularRows
import ErdosProblems.Erdos599.LadderDeferredBookkeeping
import ErdosProblems.Erdos599.SliceSpliceConstructor

/-!
# Capturing half-way height witnesses at regular ladder frontiers

This file isolates the causal closing-up and roof comparison used in
Assertion 9.9.  The half-way choice at a coordinate is made from the exact
visible stage web.  It is therefore literally the same choice as the one
registered by a sufficiently late causal row.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSliceRoofCapture

open DirectedPath

universe u

variable {V : Type u}

/-- Every ambient roof remains a roof after passing to a ladder stage web.
This local form keeps the causal capture argument independent of the later
linkage-completion modules. -/
private theorem roof_subset_stageWeb_roof
    {G : DWeb V} {kappa : Cardinal.{u}}
    (L : G.KappaLadder kappa) (delta : Ladder.Stage kappa) (T : Set V) :
    G.roof T ⊆ (L.stageWeb delta).roof T := by
  exact SliceCandidate.roof_subset_of_adj_imp G (L.stageWeb delta) rfl
    (fun {_ _} e ↦ G.quotient_adj_imp
      ((G.quotient (G.terminalFrontier (L.warpAt delta))).essentialPart_adj_imp e)) T

/-- A strict causal prefix computes the same request at every coordinate
already visible in that prefix. -/
theorem priorRequest_eq_finalRequest_of_lt
    (G : DWeb V) {kappa : Cardinal.{u}}
    (Q : RegularRows.CausalRowRule kappa V) (hkappa : ℵ₀ ≤ kappa)
    {c delta gamma : Ladder.Stage kappa}
    (hdelta : delta < c) (hgamma : gamma < c) :
    RegularRows.CausalRegular.priorRequest G hkappa c
        (fun b _hbc ↦ Q.state hkappa b) delta gamma =
      RegularRows.CausalRegular.finalRequest G Q hkappa delta gamma := by
  have hfrontier :
      (RegularRows.CausalRegular.priorLadder G c
        (fun b _hbc ↦ Q.state hkappa b)).frontier delta =
      (G.canonicalLadderCore kappa (Q.preferred hkappa)).frontier delta := by
    apply RegularRows.LadderPrefix.canonicalLadderCore_frontier_eq_of_forall_lt
    intro b hb
    exact Q.priorPreferred_eq_preferred_of_lt hkappa (hb.trans hdelta)
  ext x
  simp only [RegularRows.CausalRegular.priorRequest,
    RegularRows.CausalRegular.finalRequest,
    ControlledSlices.diagonalRequest, Set.mem_inter_iff, hfrontier]
  constructor
  · rintro ⟨hxfrontier, theta, eta, htheta, heta, hx⟩
    refine ⟨hxfrontier, theta, eta, htheta, heta, ?_⟩
    rwa [RegularRows.CausalRegular.priorEnumeration_eq_actual_of_lt
      Q hkappa (htheta.trans hgamma)] at hx
  · rintro ⟨hxfrontier, theta, eta, htheta, heta, hx⟩
    refine ⟨hxfrontier, theta, eta, htheta, heta, ?_⟩
    rwa [RegularRows.CausalRegular.priorEnumeration_eq_actual_of_lt
      Q hkappa (htheta.trans hgamma)]

/-- Every final half-way height coordinate occurs in the causal carrier.
The registering row is chosen strictly above both coordinate indices; the
stage-local choice in `SliceCandidate` then identifies the prefix choice
with the final choice. -/
theorem rowRule_registers_heightVertices
    (G : DWeb V) {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
      hG hlower F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    let L := G.canonicalLadderCore kappa
      (Q.preferred hregular.aleph0_le)
    let request := RegularRows.CausalRegular.finalRequest G Q
      hregular.aleph0_le
    ∀ delta gamma,
      SliceCandidate.heightVerticesAt hlower huncountable L request
          delta gamma ⊆ R.carrier := by
  dsimp only
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF base hbase
  let R := Q.rowSystem hregular.aleph0_le
  let L := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  let request := RegularRows.CausalRegular.finalRequest G Q
    hregular.aleph0_le
  intro delta gamma x hx
  let c : Ladder.Stage kappa :=
    ⟨max delta.1 gamma.1 + 1,
      (Cardinal.isSuccLimit_ord hregular.aleph0_le).succ_lt
        (max_lt delta.2 gamma.2)⟩
  have hdelta : delta < c := by
    change delta.1 < max delta.1 gamma.1 + 1
    exact (le_max_left delta.1 gamma.1).trans_lt (lt_add_one _)
  have hgamma : gamma < c := by
    change gamma.1 < max delta.1 gamma.1 + 1
    exact (le_max_right delta.1 gamma.1).trans_lt (lt_add_one _)
  let prior := fun b (_hbc : b < c) ↦ Q.state hregular.aleph0_le b
  let Lc := RegularRows.CausalRegular.priorLadder G c prior
  let requestc := RegularRows.CausalRegular.priorRequest G
    hregular.aleph0_le c prior
  have hwarpDelta : Lc.warpAt delta = L.warpAt delta := by
    apply RegularRows.LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
    intro b hb
    exact Q.priorPreferred_eq_preferred_of_lt hregular.aleph0_le
      (hb.trans hdelta)
  have hrequest : requestc delta gamma = request delta gamma := by
    exact priorRequest_eq_finalRequest_of_lt G Q
      hregular.aleph0_le hdelta hgamma
  have hheight :
      SliceCandidate.heightVerticesAt hlower huncountable Lc requestc
          delta gamma =
        SliceCandidate.heightVerticesAt hlower huncountable L request
          delta gamma :=
    SliceCandidate.heightVerticesAt_congr_stageData
      hlower huncountable Lc L requestc request delta gamma
        hwarpDelta hrequest
  rw [← hheight] at hx
  apply RegularRows.RowSystem.mem_carrier.2
  refine ⟨c, ?_⟩
  change x ∈ (Q.state hregular.aleph0_le c).row
  rw [Q.state_row_eq]
  change x ∈
    ((base ∪ RegularRows.pairRegistrations c
      (RegularRows.CausalRegular.pairEntry G hlower huncountable F c
        (fun b _hbc ↦ Q.state hregular.aleph0_le b))) ∪
      RegularRows.tripleRegistrations c
        (RegularRows.CausalRegular.tripleEntry G hregular.aleph0_le c
          (fun b _hbc ↦ Q.state hregular.aleph0_le b)))
  apply Or.inl
  apply Or.inr
  apply RegularRows.pair_entry_subset_registrations c _
      (⟨delta, hdelta⟩ : Set.Iio c) (⟨gamma, hgamma⟩ : Set.Iio c)
  exact Or.inr hx

/-- The chosen height set of an eligible final coordinate is contained in
the causal carrier. -/
theorem chosenHeightSet_subset_causalCarrier
    (G : DWeb V) {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
      hG hlower F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    let L := G.canonicalLadderCore kappa
      (Q.preferred hregular.aleph0_le)
    let request := RegularRows.CausalRegular.finalRequest G Q
      hregular.aleph0_le
    ∀ delta gamma,
      SliceCandidate.chosenHeightSetOfUncountable hlower huncountable L
          delta (request delta gamma) ⊆ R.carrier := by
  simpa only [SliceCandidate.heightVerticesAt] using
    rowRule_registers_heightVertices G hregular huncountable hG
      hlower F hF base hbase

/-- A pre-chosen half-way height witness is roofed by one frontier of any
prescribed club.  The conclusion is stated both in the ambient web and in
the original stage web; the latter is the input to the quotient comparison
of Assertion 9.9. -/
theorem exists_club_roof_height_of_chosen
    (G : DWeb V) {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (Sigma : Set (Ladder.Stage kappa))
    (hSigma : Stationary.IsClubBelow kappa Sigma) :
    let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
      hG hlower F hF base hbase
    let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder G kappa
      (Q.preferred hregular.aleph0_le)
    let request := RegularRows.CausalRegular.finalRequest G Q
      hregular.aleph0_le
    ∀ (delta gamma : Ladder.Stage kappa)
      (D : SliceCandidate.HalfwayPayload L delta (request delta gamma)),
      SliceCandidate.chosenHeightSetOfUncountable hlower huncountable L
          delta (request delta gamma) = D.X →
      ∃ zeta ∈ Sigma,
        D.X ⊆ G.roof (L.frontier zeta) ∧
          D.X ⊆ (L.stageWeb delta).roof (L.frontier zeta) := by
  dsimp only
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF base hbase
  let R := Q.rowSystem hregular.aleph0_le
  let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder G kappa
    (Q.preferred hregular.aleph0_le)
  let Lcore := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  let request := RegularRows.CausalRegular.finalRequest G Q
    hregular.aleph0_le
  intro delta gamma D hDX
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  have hlegal : DWeb.KappaLadder.Deferred.IsDeferredLegal L :=
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_isDeferredLegal
      (Q.preferred hregular.aleph0_le) hregular huncountable hNoEnter
  have hcarrier : R.carrier ⊆ L.limitRoof := by
    intro x hx
    obtain ⟨a, ha⟩ := Q.exists_preferred_eq_some_of_mem_carrier
      hregular huncountable hx
    let b : Ladder.Stage kappa :=
      ⟨a.1 + 1, (Cardinal.isSuccLimit_ord hregular.aleph0_le).succ_lt a.2⟩
    exact DWeb.KappaLadder.canonicalLadderCore_preferred_mem_limitRoof_of_fields
      (Q.preferred hregular.aleph0_le) hG hlegal.freshMarkers
        hlegal.waveRungs hlegal.exactSuccessorArrows
        hlegal.roofsSourceAtStages a b rfl ha
  have hgeometry : SliceSpliceConstructor.SpliceLadderGeometry G L :=
    ⟨hregular,
      DWeb.KappaLadder.Deferred.IsDeferredLegal.initialStage hlegal,
      DWeb.KappaLadder.Deferred.IsDeferredLegal.limitStages hlegal,
      DWeb.KappaLadder.Deferred.IsDeferredLegal.warpStages hlegal,
      DWeb.KappaLadder.Deferred.IsDeferredLegal.frontiersEssential hlegal,
      DWeb.KappaLadder.Deferred.IsDeferredLegal.frontierChronology hlegal,
      DWeb.KappaLadder.Deferred.IsDeferredLegal.strictFrontierChronology hlegal⟩
  have hroofed : SliceSpliceConstructor.IsEventuallyRoofed G L R.carrier :=
    SliceSpliceConstructor.isEventuallyRoofed_of_subset_limitRoof
      hgeometry hcarrier
  have hXcarrier : D.X ⊆ R.carrier := by
    rw [← hDX]
    change SliceCandidate.chosenHeightSetOfUncountable
        hlower huncountable Lcore delta (request delta gamma) ⊆ R.carrier
    exact chosenHeightSet_subset_causalCarrier G hregular huncountable hG
      hlower F hF base hbase delta gamma
  obtain ⟨zeta, hzeta, hXzeta⟩ :=
    SliceSpliceConstructor.exists_club_roof_superset hregular hSigma
      hroofed hXcarrier D.heightSmall
  refine ⟨zeta, hzeta, hXzeta, ?_⟩
  exact hXzeta.trans (roof_subset_stageWeb_roof L delta (L.frontier zeta))

/-- The chosen half-way stop-over is roofed by a strictly later member of
the prescribed club.  This is the causal form of source Assertion 9.9:
first close the small chosen height set at a club frontier, move once more
inside the club, and apply the maximal-rung quotient comparison to the
height wave carried by the payload. -/
theorem exists_later_club_roof_halfwayPayload_of_chosen
    (G : DWeb V) {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (Sigma : Set (Ladder.Stage kappa))
    (hSigma : Stationary.IsClubBelow kappa Sigma) :
    let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
      hG hlower F hF base hbase
    let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder G kappa
      (Q.preferred hregular.aleph0_le)
    let request := RegularRows.CausalRegular.finalRequest G Q
      hregular.aleph0_le
    ∀ (delta gamma : Ladder.Stage kappa)
      (D : SliceCandidate.HalfwayPayload L delta (request delta gamma)),
      SliceCandidate.chosenHeightSetOfUncountable hlower huncountable L
          delta (request delta gamma) = D.X →
      ∃ beta ∈ Sigma, delta < beta ∧
        D.C ⊆ (L.stageWeb delta).roof (L.frontier beta) := by
  dsimp only
  let Q := RegularRows.CausalRegular.rowRule G hregular huncountable
    hG hlower F hF base hbase
  let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder G kappa
    (Q.preferred hregular.aleph0_le)
  let request := RegularRows.CausalRegular.finalRequest G Q
    hregular.aleph0_le
  intro delta gamma D hDX
  obtain ⟨zeta0, _hzeta0Sigma, hXzeta0, _hXzeta0Stage⟩ :=
    exists_club_roof_height_of_chosen G hregular huncountable hG
      hlower F hF base hbase Sigma hSigma delta gamma D hDX
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  have hlegal : DWeb.KappaLadder.Deferred.IsDeferredLegal L :=
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_isDeferredLegal
      (Q.preferred hregular.aleph0_le) hregular huncountable hNoEnter
  let zeta := RegularCardinal.aboveInClub hregular Sigma hSigma delta zeta0
  have hdeltaZeta : delta < zeta :=
    RegularCardinal.left_lt_aboveInClub hregular Sigma hSigma delta zeta0
  have hzeta0Zeta : zeta0 < zeta :=
    RegularCardinal.right_lt_aboveInClub hregular Sigma hSigma delta zeta0
  have hXzetaAmbient : D.X ⊆ G.roof (L.frontier zeta) :=
    hXzeta0.trans (G.roof_cut
      (DWeb.KappaLadder.Deferred.IsDeferredLegal.frontierChronology
        hlegal hzeta0Zeta))
  have hXzeta : D.X ⊆
      (L.stageWeb delta).roof (L.frontier zeta) :=
    hXzetaAmbient.trans
      (roof_subset_stageWeb_roof L delta (L.frontier zeta))
  let beta := RegularCardinal.nextInClub hregular Sigma hSigma zeta
  have hbetaSigma : beta ∈ Sigma :=
    RegularCardinal.nextInClub_mem hregular Sigma hSigma zeta
  have hzetaBeta : zeta < beta :=
    RegularCardinal.lt_nextInClub hregular Sigma hSigma zeta
  have hheightGeometry : SliceCandidate.HeightRoofGeometry L :=
    ⟨DWeb.KappaLadder.Deferred.IsDeferredLegal.waveRungs hlegal,
      DWeb.KappaLadder.Deferred.IsDeferredLegal.roofMaximalRungs hlegal,
      DWeb.KappaLadder.Deferred.IsDeferredLegal.exactSuccessorArrows hlegal,
      DWeb.KappaLadder.Deferred.IsDeferredLegal.roofsSourceAtStages hlegal,
      DWeb.KappaLadder.Deferred.IsDeferredLegal.frontierChronology hlegal⟩
  have hterminalLift :=
    SliceCandidate.quotientStageWave_terminalFrontier_subset_laterFrontierRoof_of_geometry
      hheightGeometry hNoEnter hdeltaZeta hzetaBeta hXzeta D.heightWave
  have hterminal :
      ((L.stageWeb delta).quotient D.X).terminalFrontier D.R ⊆
        (L.stageWeb delta).roof (L.frontier beta) := by
    simpa only [(L.stageWeb delta).terminalFrontier_liftQuotientFamily]
      using hterminalLift
  refine ⟨beta, hbetaSigma, hdeltaZeta.trans hzetaBeta, ?_⟩
  exact D.stopoverRoof.trans ((L.stageWeb delta).roof_cut hterminal)

end RegularSliceRoofCapture
end CardinalInduction
end Erdos599
