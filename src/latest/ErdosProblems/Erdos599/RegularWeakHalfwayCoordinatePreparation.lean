/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularWeakHalfwayRoofCapture
import ErdosProblems.Erdos599.HeightRoofBridge

/-!
# Preparing a registered half-way coordinate

The half-way payload and the carrier of its request-rooted components are
chosen before the later annular boundary.  One club stage first captures
that registered set in its roof.  A second club stage is then chosen above
the first; Assertion 9.9 puts the stop-over below this second frontier, while
frontier chronology keeps the selected carrier roofed there as well.

This module contains only that quantifier and chronology calculation.  It
does not assert that the selected target track is disjoint from a subsequently
chosen clean continuation.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakHalfwayCoordinatePreparation

open SliceSpliceSource

universe u

variable {V : Type u}

/-- A causally registered half-way payload admits two ordered club stages:
the first roofs its registered height/selected carrier, and the second roofs
both the stop-over (in the old stage web) and the selected carrier (in the
ambient web).  Membership of the second stage in a club disjoint from `phi`
also supplies the ordinary-stage smallness side condition. -/
theorem halfwayPayload_exists_later_roofed_coordinate
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (hNorm : Gamma.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    {Z : Set V} (hZroof : Z ⊆ L.limitRoof)
    {delta gamma : Ladder.Stage kappa}
    (D : SliceCandidate.HalfwayPayload L delta (request delta gamma))
    (hregistration :
      RegularWeakHalfwayRegistration.registrationAt hlower
          hL.uncountable L request delta gamma =
        D.X ∪ (L.stageWeb delta).vertexSet
          (initialRestriction (L.stageWeb delta) D.W
            (request delta gamma)))
    (hregistered :
      RegularWeakHalfwayRegistration.registrationAt hlower
        hL.uncountable L request delta gamma ⊆ Z) :
    ∃ zeta ∈ Sigma, ∃ beta ∈ Sigma,
      delta < zeta ∧ zeta < beta ∧ beta ∉ L.phi ∧
        D.C ⊆ (L.stageWeb delta).roof (L.frontier beta) ∧
        (L.stageWeb delta).vertexSet
            (initialRestriction (L.stageWeb delta) D.W
              (request delta gamma)) ⊆
          Gamma.roof (L.frontier beta) := by
  obtain ⟨zeta, hzeta, hdeltaZeta, hroofZeta⟩ :=
    RegularWeakHalfwayRoofCapture.exists_later_club_roof_superset_registrationAt
      hregular hlower hL hSigma request hZroof delta gamma hregistered
  let beta := RegularCardinal.aboveInClub hregular Sigma hSigma zeta zeta
  have hbeta : beta ∈ Sigma :=
    RegularCardinal.aboveInClub_mem hregular Sigma hSigma zeta zeta
  have hzetaBeta : zeta < beta :=
    RegularCardinal.left_lt_aboveInClub hregular Sigma hSigma zeta zeta
  have hbetaNotPhi : beta ∉ L.phi := by
    intro hbetaPhi
    exact Set.disjoint_left.1 havoid hbeta hbetaPhi
  have hXzeta : D.X ⊆ Gamma.roof (L.frontier zeta) := by
    intro x hx
    apply hroofZeta
    rw [hregistration]
    exact Or.inl hx
  have hselectedZeta :
      (L.stageWeb delta).vertexSet
          (initialRestriction (L.stageWeb delta) D.W
            (request delta gamma)) ⊆
        Gamma.roof (L.frontier zeta) := by
    intro x hx
    apply hroofZeta
    rw [hregistration]
    exact Or.inr hx
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hCroof :
      D.C ⊆ (L.stageWeb delta).roof (L.frontier beta) :=
    by
      have hXzetaStage :
          D.X ⊆ (L.stageWeb delta).roof (L.frontier zeta) :=
        hXzeta.trans
          (SliceCandidate.roof_subset_of_adj_imp Gamma
            (L.stageWeb delta) rfl
            (fun {_ _} e ↦ Gamma.quotient_adj_imp
              ((Gamma.quotient
                (Gamma.terminalFrontier (L.warpAt delta)))
                  |>.essentialPart_adj_imp e))
            (L.frontier zeta))
      have hterminalLift :=
        SliceCandidate.quotientStageWave_terminalFrontier_subset_laterFrontierRoof_of_geometry
          (SliceCandidate.HeightRoofGeometry.ofSplitLegal hL) hNoEnter
            hdeltaZeta hzetaBeta hXzetaStage D.heightWave
      have hterminal :
          ((L.stageWeb delta).quotient D.X).terminalFrontier D.R ⊆
            (L.stageWeb delta).roof (L.frontier beta) := by
        simpa only
          [(L.stageWeb delta).terminalFrontier_liftQuotientFamily]
          using hterminalLift
      exact D.stopoverRoof.trans
        ((L.stageWeb delta).roof_cut hterminal)
  have hselectedBeta :
      (L.stageWeb delta).vertexSet
          (initialRestriction (L.stageWeb delta) D.W
            (request delta gamma)) ⊆
        Gamma.roof (L.frontier beta) := by
    exact hselectedZeta.trans
      (Gamma.roof_cut (hL.frontierChronology hzetaBeta))
  exact ⟨zeta, hzeta, beta, hbeta, hdeltaZeta, hzetaBeta,
    hbetaNotPhi, hCroof, hselectedBeta⟩

/-- Recover the registered payload and perform the two-stage roof capture in
one step.  This is the provider-facing form: causal row closure supplies
`hregistered`, while half-way eligibility supplies the payload. -/
theorem exists_halfwayPayload_later_roofed_coordinate
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (hNorm : Gamma.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    {Z : Set V} (hZroof : Z ⊆ L.limitRoof)
    (delta gamma : Ladder.Stage kappa)
    (heligible : SliceCandidate.HalfwayChoiceEligible L delta
      (request delta gamma))
    (hregistered :
      RegularWeakHalfwayRegistration.registrationAt hlower
        hL.uncountable L request delta gamma ⊆ Z) :
    ∃ D : SliceCandidate.HalfwayPayload L delta (request delta gamma),
      ∃ zeta ∈ Sigma, ∃ beta ∈ Sigma,
        delta < zeta ∧ zeta < beta ∧ beta ∉ L.phi ∧
          D.X ∪ (L.stageWeb delta).vertexSet
              (initialRestriction (L.stageWeb delta) D.W
                (request delta gamma)) ⊆ Z ∧
          D.C ⊆ (L.stageWeb delta).roof (L.frontier beta) ∧
          (L.stageWeb delta).vertexSet
              (initialRestriction (L.stageWeb delta) D.W
                (request delta gamma)) ⊆
            Gamma.roof (L.frontier beta) := by
  obtain ⟨D, hregistration⟩ :=
    RegularWeakHalfwayRegistration.exists_halfwayPayload_with_registration
      hlower hL.uncountable L request delta gamma heligible
  obtain ⟨zeta, hzeta, beta, hbeta, hdeltaZeta, hzetaBeta,
      hbetaNotPhi, hCroof, hselectedBeta⟩ :=
    halfwayPayload_exists_later_roofed_coordinate hregular hNorm hlower hL
      hSigma havoid request hZroof D hregistration hregistered
  refine ⟨D, zeta, hzeta, beta, hbeta, hdeltaZeta, hzetaBeta,
    hbetaNotPhi, ?_, hCroof, hselectedBeta⟩
  rw [← hregistration]
  exact hregistered

end RegularWeakHalfwayCoordinatePreparation
end CardinalInduction
end Erdos599
