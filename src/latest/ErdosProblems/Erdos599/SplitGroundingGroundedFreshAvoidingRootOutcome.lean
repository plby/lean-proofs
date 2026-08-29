/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingControlNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedRootOutcome

/-!
# Canonical fresh-avoiding root outcome

The canonical pre-stopped dispatcher is combined with the total control
normalizer.  A root obstruction is therefore either a selected-owner leaf,
or (after every control is genuinely rooted) one of the exact finite-source
or blocking outcomes.  The boundary obstruction remains separate for the
global priority exchange.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

/-- Fully concrete canonical dispatcher in the nonstationary-fresh branch. -/
theorem splitGroundedFreshAvoidingCanonicalAssertion822Output_or_normalizedObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (hnotFresh : ¬ Stationary.IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) ∨
      L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) ∨
      L.SplitGroundedRootFailureAfterControls
        (L.splitGroundedFreshAvoidingCanonicalUnusedRecord
          hL hground hnotFresh S) ∨
      Nonempty (L.SplitGroundedPreStoppedBoundaryObstruction
        (L.splitGroundedFreshAvoidingCanonicalUnusedRecord
          hL hground hnotFresh S)) := by
  let R := L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S
  rcases L.splitGroundedFreshAvoidingCanonicalAssertion822Output_or_obstruction
      hL hground hnotFresh S with houtput | hroot | hboundary
  · exact Or.inl houtput
  · let O := hroot.some
    rcases L.splitGroundedFreshAvoiding_controls_rooted_or_normalized
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) with hcontrols | hnormalized
    · right
      right
      left
      exact O.failureAfterControls R hcontrols
    · exact Or.inr (Or.inl hnormalized)
  · exact Or.inr (Or.inr (Or.inr hboundary))

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoidingCanonicalAssertion822Output_or_normalizedObstruction
