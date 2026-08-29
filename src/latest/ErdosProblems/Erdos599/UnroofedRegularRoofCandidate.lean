/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerSliceGeometry
import ErdosProblems.Erdos599.UnroofedRegularRowClosure
import ErdosProblems.Erdos599.RegularLocalizedProtectedRoofCandidate

/-!
# Populated protected coordinates on the actual unroofed ladder

The genuine causal carrier roofs the exact chosen registration. Two later
club stages then supply the existing height transport and clean-candidate
compiler, using only the proved marker-independent slice geometry.
-/

noncomputable section

namespace Erdos599.CardinalInduction.UnroofedRegularRows

open Set Cardinal RegularRows
open RegularProtectedAmbientRebuild SingularProtectedLowerSelection

universe u

variable {V : Type u} (G : DWeb V) {kappa : Cardinal.{u}}

theorem exists_later_club_roof_registrationAt
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (Q : CausalRowRule kappa V)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    {Sigma : Set (Ladder.Stage kappa)} (hSigma : Stationary.IsClubBelow kappa Sigma)
    (delta gamma : Ladder.Stage kappa)
    (hregistered : RegularLocalizedProtectedRegistration.registrationAt
        (DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le) request delta gamma ⊆
      (Q.rowSystem hregular.aleph0_le).carrier) :
    ∃ zeta ∈ Sigma, delta < zeta ∧
      RegularLocalizedProtectedRegistration.registrationAt
          (DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le) request delta gamma ⊆
        G.roof ((DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le).frontier zeta) := by
  let L := DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hgeometry := DWeb.UnroofedMarker.ladder_spliceGeometry G kappa
    (Q.preferred hregular.aleph0_le) hNoEnter hregular
  have hcarrier : (Q.rowSystem hregular.aleph0_le).carrier ⊆ L.limitRoof :=
    DWeb.UnroofedMarker.causalCarrier_subset_limitRoof G Q hNoEnter hregular huncountable
  have hroofed := SliceSpliceConstructor.isEventuallyRoofed_of_subset_limitRoof
    hgeometry hcarrier
  have hsmall : #(RegularLocalizedProtectedRegistration.registrationAt L request delta gamma) <
      kappa := RegularLocalizedProtectedRegistration.mk_registration_lt hregular huncountable
        (RegularCandidateProvider.stageWeb_isNormalized hNorm L delta)
  obtain ⟨a, _haSigma, hZa⟩ := SliceSpliceConstructor.exists_club_roof_superset
    hregular hSigma hroofed hregistered hsmall
  let zeta := RegularCardinal.aboveInClub hregular Sigma hSigma delta a
  have hzeta : zeta ∈ Sigma := RegularCardinal.aboveInClub_mem hregular Sigma hSigma delta a
  have hdelta : delta < zeta :=
    RegularCardinal.left_lt_aboveInClub hregular Sigma hSigma delta a
  have ha : a < zeta := RegularCardinal.right_lt_aboveInClub hregular Sigma hSigma delta a
  exact ⟨zeta, hzeta, hdelta, hZa.trans (G.roof_cut (hgeometry.frontierChronology ha))⟩

/-- The exact visible candidate table is nonempty at a later club coordinate.
Lower induction is used on edge subwebs of the same ambient graph. -/
theorem exists_later_candidate_of_lower
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (hext : ExtensionBelowFor G kappa)
    (hhalf : ProtectedHalfwayBelowFor G kappa)
    (F : Set G.DPath) (hF : G.IsWarp F) (base : Set V) (hbase : #base ≤ kappa)
    {Sigma : Set (Ladder.Stage kappa)} (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid :
      let Q := rowRule G hregular huncountable hNorm F hF base hbase
      Disjoint Sigma (DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le).phi)
    (delta gamma : Ladder.Stage kappa)
    (hstage :
      let Q := rowRule G hregular huncountable hNorm F hF base hbase
      ((DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le).stageWeb delta).IsUnhindered) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let L := DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le
    ∃ beta ∈ Sigma, delta < beta ∧ ∃ P : RegularWeakSplitCandidate.WeakSplitFamilies G,
      RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
        G L (finalRequest G Q hregular.aleph0_le) delta beta gamma P := by
  dsimp only at hstage havoid ⊢
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let L := DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le
  let request := finalRequest G Q hregular.aleph0_le
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hL : L.SliceGeometry := DWeb.UnroofedMarker.ladder_sliceGeometry G kappa
    (Q.preferred hregular.aleph0_le) hNoEnter hregular huncountable
  have hrequest : request delta gamma ⊆ (L.stageWeb delta).source := Set.inter_subset_left
  have hrequestSmall : #(request delta gamma) < kappa :=
    ControlledSlices.mk_diagonalRequest_lt hregular _ _ _ _
  have hQBase : ∀ {x y : V}, (L.stageWeb delta).graph.Adj x y → G.graph.Adj x y := by
    intro x y hxy
    exact G.quotient_adj_imp
      ((G.quotient (G.terminalFrontier (L.warpAt delta))).essentialPart_adj_imp hxy)
  have hNormStage : (L.stageWeb delta).IsNormalized :=
    RegularCandidateProvider.stageWeb_isNormalized hNorm L delta
  have hwitness := RegularLocalizedProtectedSelection.exists_witness_with_registration_of_lower
    huncountable hext hhalf hQBase hNormStage hstage hrequest hrequestSmall
  have hregistered : RegularLocalizedProtectedRegistration.registrationAt L request delta gamma ⊆
      (Q.rowSystem hregular.aleph0_le).carrier :=
    registrationAt_subset_carrier G hregular huncountable hNorm F hF base hbase delta gamma
  obtain ⟨zeta, hzeta, hdelta, hregistrationRoof⟩ :=
    exists_later_club_roof_registrationAt G hregular huncountable hNorm Q request
      hSigma delta gamma hregistered
  exact RegularLocalizedProtectedRoofCandidate.exists_later_candidate_of_registrationWitness
    hL hNorm hext hSigma havoid hdelta hzeta hregistrationRoof hwitness hrequest

#print axioms exists_later_club_roof_registrationAt
#print axioms exists_later_candidate_of_lower

end Erdos599.CardinalInduction.UnroofedRegularRows
