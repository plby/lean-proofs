/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalGlobalHammockClosure
import ErdosProblems.Erdos599.HalfwayMovingBetaRecordedReservoir

/-!
# Feeding the causal global carrier into the moving 9.31 closure

This module is the direct bridge from the simultaneous causal ladder/set
construction to the already established small moving-`beta` closure.  The
only identification required is that the club-stage package uses that same
canonical causal ladder; no global hammock or reference-closure premise is
left to the caller.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating Ladder Blueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace CausalSection9Rows

/-- Extract the small, transaction-specific dynamic closure from the
concrete causal global carrier. -/
theorem exists_dynamicMoving931GlobalClosure
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (X0 : Set V)
    (hX0 : X0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hX0card : #X0 ≤ kappa) :
    Nonempty (DynamicMoving931GlobalClosure C
      (globalCarrier Gamma kappa hkappa hGamma seed hseed) X0) := by
  apply DynamicMoving931GlobalClosure.exists_of_globalClosedSet C
    (globalCarrier Gamma kappa hkappa hGamma seed hseed) X0
  · simpa only [hC] using
      (globalCarrier_subset_limitRoof
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
  · simpa only [hC] using
      (hammockClosed_limitWarp
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
  · simpa only [hC] using
      (reference_closed
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
  · exact hX0
  · exact hX0card

/-- The countable moving-`beta` iteration is likewise unconditional once
the club package is known to use the causal ladder.  Record and marker
reservoir hypotheses are discharged by their actual successor history
rows. -/
theorem exists_movingBetaOmegaClosure
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (X0 : Set V)
    (hX0 : X0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    (hX0card : #X0 ≤ kappa) :
    Nonempty (MovingBetaOmegaClosure C
      (globalCarrier Gamma kappa hkappa hGamma seed hseed) X0
      (fun b ↦ C.movingReferenceDifference C.newStage b)) := by
  apply MovingBetaOmegaClosure.exists_of_recorded_marker_reservoir C
    (globalCarrier Gamma kappa hkappa hGamma seed hseed) X0
  · simpa only [hC] using
      (globalCarrier_subset_limitRoof
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
  · simpa only [hC] using
      (hammockClosed_limitWarp
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
  · simpa only [hC] using
      (reference_closed
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
  · intro a p hp
    apply chosen_support_subset_globalCarrier
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed
    simpa only [hC] using hp
  · simpa only [hC] using
      (markerSet_subset_globalCarrier
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed)
  · exact hX0
  · exact hX0card

#print axioms CausalSection9Rows.exists_dynamicMoving931GlobalClosure
#print axioms CausalSection9Rows.exists_movingBetaOmegaClosure

end CausalSection9Rows
end Erdos599.Blueprint.LinkageBlueprint

