/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularEnrichedExactFullRow
import ErdosProblems.Erdos599.RegularExactWeakRowExtension
import ErdosProblems.Erdos599.RegularWeakSource915Rows

/-!
# Packaging the enriched exact row as an annular candidate

The exact-frontier construction is performed inside the stage web.  This
module records the short ambient transport which turns its enriched output
into the literal candidate predicate used by the regular causal table.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularEnrichedExactCandidate

open SliceCandidate SliceSpliceSource

universe u

variable {V : Type u}

/-- An exact half-way payload at a captured later frontier produces the
ambient annular candidate stored at that coordinate. -/
theorem HalfwayPayload.exists_annularSliceCandidate_of_exactFrontier
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal)
    (hNorm : Gamma.IsNormalized)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    {delta beta gamma : Ladder.Stage kappa} (hdeltaBeta : delta < beta)
    (hbeta : beta ∉ L.phi)
    (D : HalfwayPayload L delta (request delta gamma))
    (hrequest : request delta gamma ⊆ L.frontier delta)
    (hsmall : #(request delta gamma) < kappa)
    (hCroof : D.C ⊆ (L.stageWeb delta).roof (L.frontier beta))
    (hexact : (L.stageWeb delta).terminalFrontier D.W = D.C) :
    ∃ T : Set Gamma.DPath,
      IsAnnularSliceCandidate Gamma L request delta beta gamma T := by
  obtain ⟨W, hW, hlinks, hregion, hmavericks⟩ :=
    RegularEnrichedExactFullRow.HalfwayPayload.exists_enrichedTargetLinkingAnnular_of_exactFrontier
      hlower hregular huncountable hL hNorm hdeltaBeta hbeta D
        hrequest hsmall hCroof hexact
  let T := SliceSegmentCore.liftStageFamily L delta W
  have hlinkage : IsLinkageBetween Gamma (L.frontier delta)
      (L.frontier beta) T := by
    exact SliceDeltaLift.IsLinkageBetween.liftStageFamily hW.1
  have htight : MeetsOnlyAtTerminal Gamma T (L.frontier beta) := by
    exact SliceDeltaLift.meetsOnlyAtTerminal_liftStageFamily hW.2
  have hlinksAmbient : LinksToTarget Gamma T (request delta gamma) := by
    exact SliceSegmentCore.linksToTarget_liftStageFamily L delta hlinks
  have hintervals : HasStageIntervalSegments Gamma L T delta beta :=
    SliceCandidate.linkage_hasStageIntervalSegments
      hL hdeltaBeta.le hlinkage
  refine ⟨T, ?_, hintervals, ?_⟩
  · exact ⟨⟨⟨hlinkage, hlinksAmbient⟩, hregion⟩, htight⟩
  · exact hmavericks

/-- The enhanced causal row has the exact infinite-frontier coordinate
provider required by the regular assembly.  All choices are made through
the causally registered exact half-way payload. -/
theorem hasExactAnnularCoordinateProvider
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized)
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    RegularExtension.HasExactAnnularCoordinateProvider G hregular
      huncountable hNorm hlower F hF base hbase := by
  let lower := hlower.toUniversalCardinalInductionBelow
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
    huncountable hNorm lower F hF base hbase
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  let request := RegularRows.CausalRegular.finalRequest G Q
    hregular.aleph0_le
  intro Sigma hSigma havoid delta hstage hinfinite gamma
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hL : L.IsLegal :=
    DWeb.KappaLadder.canonicalLadderWithBookkeeping_isLegal
      (Q.preferred hregular.aleph0_le) hregular huncountable hNoEnter
  have hrequest : request delta gamma ⊆ L.frontier delta :=
    RegularExtension.finalRequest_subset_frontier
      (G := G) Q hregular.aleph0_le delta gamma
  have hsmall : #(request delta gamma) < kappa :=
    RegularExtension.mk_finalRequest_lt (G := G) Q hregular delta gamma
  have heligible : HalfwayChoiceEligible L delta
      (request delta gamma) :=
    ⟨hstage, hrequest, hsmall, hinfinite⟩
  have hZroof : (Q.rowSystem hregular.aleph0_le).carrier ⊆
      L.limitRoof :=
    RegularWeakSplitRowClosure.carrier_subset_limitRoof G hregular
      huncountable hNorm lower F hF base hbase
  let Lcore := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  have hregisteredCore :
      RegularWeakHalfwayRegistration.registrationAt lower huncountable
          Lcore request delta gamma ⊆
        (Q.rowSystem hregular.aleph0_le).carrier := by
    simpa only [Lcore, request, Q] using
      (RegularRows.CausalRegular.halfwayRegistrationAt_subset_weakSplitRowRule_carrier
        G hregular huncountable hNorm lower F hF base hbase delta gamma)
  have hwarp : Lcore.warpAt delta = L.warpAt delta := by
    simp only [L, Lcore, DWeb.KappaLadder.canonicalLadder,
      DWeb.KappaLadder.withValidBookkeeping_warpAt]
  have hregistered :
      RegularWeakHalfwayRegistration.registrationAt lower huncountable
          L request delta gamma ⊆
        (Q.rowSystem hregular.aleph0_le).carrier :=
    by
      rw [← RegularWeakHalfwayRegistration.registrationAt_congr_stageData
        lower huncountable hwarp rfl]
      exact hregisteredCore
  obtain ⟨D, hexact, zeta, hzeta, beta, hbeta, hdeltaZeta,
      hzetaBeta, hbetaNotPhi, _hregisteredD, hCroof,
      _hselectedRoof⟩ :=
    RegularExactHalfwayCoordinate.exists_exactHalfwayPayload_later_roofed_coordinate
      hregular hNorm hlower hL hSigma havoid request hZroof delta gamma
        heligible hregistered
  have hdeltaBeta : delta < beta := hdeltaZeta.trans hzetaBeta
  obtain ⟨T, hT⟩ :=
    HalfwayPayload.exists_annularSliceCandidate_of_exactFrontier
      lower hregular huncountable hL hNorm request hdeltaBeta
        hbetaNotPhi D hrequest hsmall hCroof hexact
  exact ⟨beta, hbeta, hdeltaBeta, T, hT⟩

#print axioms HalfwayPayload.exists_annularSliceCandidate_of_exactFrontier
#print axioms hasExactAnnularCoordinateProvider

end RegularEnrichedExactCandidate
end CardinalInduction
end Erdos599
