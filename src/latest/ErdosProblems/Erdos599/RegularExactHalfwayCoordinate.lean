/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularExactHalfwayRegistration
import ErdosProblems.Erdos599.RegularWeakHalfwayCoordinatePreparation
import ErdosProblems.Erdos599.RegularExactHalfwayPayload

/-!
# Exact-frontier causal half-way coordinates

The existing weak row now prefers an exact-frontier registration whenever
the exact lower induction supplies one.  This file recovers that literal
payload from the completed row and performs the two-stage club roof capture.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExactHalfwayCoordinate

open SliceSpliceSource

universe u

variable {V : Type u}

/-- Provider-facing exact version of the registered half-way roof capture. -/
theorem exists_exactHalfwayPayload_later_roofed_coordinate
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (hNorm : Gamma.IsNormalized)
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    {Z : Set V} (hZroof : Z ⊆ L.limitRoof)
    (delta gamma : Ladder.Stage kappa)
    (heligible : SliceCandidate.HalfwayChoiceEligible L delta
      (request delta gamma))
    (hregistered :
      RegularWeakHalfwayRegistration.registrationAt
        hlower.toUniversalCardinalInductionBelow hL.uncountable
          L request delta gamma ⊆ Z) :
    ∃ D : SliceCandidate.HalfwayPayload L delta (request delta gamma),
      (L.stageWeb delta).terminalFrontier D.W = D.C ∧
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
  let hlowerOrdinary := hlower.toUniversalCardinalInductionBelow
  obtain ⟨D, hexact, hregistration⟩ :=
    RegularExactHalfwayRegistration.exists_exactHalfwayPayload_with_weakRegistration
      hlower hL.uncountable L request delta gamma heligible
  obtain ⟨zeta, hzeta, beta, hbeta, hdeltaZeta, hzetaBeta,
      hbetaNotPhi, hCroof, hselectedBeta⟩ :=
    RegularWeakHalfwayCoordinatePreparation.halfwayPayload_exists_later_roofed_coordinate
      hregular hNorm hlowerOrdinary hL hSigma havoid request hZroof D
        hregistration hregistered
  refine ⟨D, hexact, zeta, hzeta, beta, hbeta, hdeltaZeta, hzetaBeta,
    hbetaNotPhi, ?_, hCroof, hselectedBeta⟩
  rw [← hregistration]
  exact hregistered

/-- At the captured coordinate, the recovered exact payload produces one
joint target-linking annular stage row. -/
theorem exists_targetLinkingAnnular_later_coordinate
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (hNorm : Gamma.IsNormalized)
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    {Z : Set V} (hZroof : Z ⊆ L.limitRoof)
    (delta gamma : Ladder.Stage kappa)
    (heligible : SliceCandidate.HalfwayChoiceEligible L delta
      (request delta gamma))
    (hregistered :
      RegularWeakHalfwayRegistration.registrationAt
        hlower.toUniversalCardinalInductionBelow hL.uncountable
          L request delta gamma ⊆ Z) :
    ∃ beta ∈ Sigma, delta < beta ∧ beta ∉ L.phi ∧
      ∃ W : Set (L.stageWeb delta).DPath,
        IsLinkageBetween (L.stageWeb delta) (L.frontier delta)
            (L.frontier beta) W ∧
          LinksToTarget (L.stageWeb delta) W (request delta gamma) := by
  obtain ⟨D, hexact, zeta, _hzeta, beta, hbeta, hdeltaZeta,
      hzetaBeta, hbetaNotPhi, _hregisteredD, hCroof, _hselectedRoof⟩ :=
    exists_exactHalfwayPayload_later_roofed_coordinate hregular hNorm
      hlower hL hSigma havoid request hZroof delta gamma heligible
        hregistered
  obtain ⟨W, hW, hlinks⟩ :=
    RegularExactHalfwayPayload.HalfwayPayload.exists_targetLinkingAnnular_of_exactFrontier
      hlower.toUniversalCardinalInductionBelow hregular hL.uncountable
        hL hNorm (hdeltaZeta.trans hzetaBeta) hbetaNotPhi D
          heligible.request_subset heligible.request_small hCroof hexact
  exact ⟨beta, hbeta, hdeltaZeta.trans hzetaBeta, hbetaNotPhi,
    W, hW, hlinks⟩

end RegularExactHalfwayCoordinate
end CardinalInduction
end Erdos599
