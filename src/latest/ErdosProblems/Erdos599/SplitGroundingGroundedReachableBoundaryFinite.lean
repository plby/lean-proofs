/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReachableBoundaryNormal
import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryFinite

/-!
# Finite-terminal normalization of the reachable grounded boundary

This refines the public reachable first-hit owner pair at its only finite
later endpoint.  A blocker-to-finite collision is no longer represented by
an arbitrary switched reachability witness: it is either a residual
fragment-terminal collision or a selected active edge leaving exactly at
the blocker.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingErasedDecode PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev ReachableRecord :=
  L.splitGroundedCanonicalUnusedRecord hL hground S

/-- The reachable first-hit boundary form after eliminating the coarse
blocking-to-finite case.  All constructors retain the exact endpoint owner
data, while the finite-later cases expose the stronger terminal/departure
geometry. -/
inductive SplitGroundedReachableBoundaryFiniteOutcome
    (O : L.SplitGroundedReachableBoundaryObstruction
      (ReachableRecord (L := L) (hL := hL)
        (hground := hground) (S := S))) : Prop
  | earlierControl
      (D : L.SplitGroundedReachableFirstBoundaryReduction O)
      (old : oldRequests
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
      (value_eq : old.1 = D.core.reduced.earlier)
      (departure : SplitGroundedFirstBoundaryDepartureOutcome D.core)
      (later_owner : SplitGroundedBBPointOwner
        (L := L) (hL := hL) (hground := hground) (S := S)
          D.core.reduced.later)
  | blockingFiniteTerminal
      (D : L.SplitGroundedReachableFirstBoundaryReduction O)
      (terminal : SplitGroundedBlockingFiniteTerminalCase D.core.reduced)
  | blockingFiniteSelectedDeparture
      (D : L.SplitGroundedReachableFirstBoundaryReduction O)
      (P : (L.splitGroundedPopularAuxiliaryInput hL.legal).Fragment)
      (fragment_mem : P ∈ GroundingCut.G0
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
      (blockable : GroundingCut.IsBlockable
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut P)
      (point_eq : GroundingCut.blockingPoint
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut P =
          D.core.reduced.earlier)
      (later_finite : D.core.reduced.later ∈
        (L.splitGroundedPopularAuxiliaryInput hL.legal).finiteSource)
      (later_cut : PopularAuxiliary.Input.LambdaVertex.old
        D.core.reduced.later ∈ S.cut)
      (departure : SplitGroundedSelectedDepartureAtBlocker D.core)
  | blockingToControl
      (D : L.SplitGroundedReachableFirstBoundaryReduction O)
      (P : (L.splitGroundedPopularAuxiliaryInput hL.legal).Fragment)
      (fragment_mem : P ∈ GroundingCut.G0
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
      (blockable : GroundingCut.IsBlockable
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut P)
      (point_eq : GroundingCut.blockingPoint
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut P =
          D.core.reduced.earlier)
      (point_mem_support : D.core.reduced.earlier ∈ P.path.support)
      (departure : SplitGroundedFirstBoundaryDepartureOutcome D.core)
      (old : oldRequests
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
      (value_eq : old.1 = D.core.reduced.later)
  | blockingToBlocking
      (D : L.SplitGroundedReachableFirstBoundaryReduction O)
      (P : (L.splitGroundedPopularAuxiliaryInput hL.legal).Fragment)
      (fragment_mem : P ∈ GroundingCut.G0
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
      (blockable : GroundingCut.IsBlockable
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut P)
      (point_eq : GroundingCut.blockingPoint
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut P =
          D.core.reduced.earlier)
      (point_mem_support : D.core.reduced.earlier ∈ P.path.support)
      (departure : SplitGroundedFirstBoundaryDepartureOutcome D.core)
      (Q : (L.splitGroundedPopularAuxiliaryInput hL.legal).Fragment)
      (later_fragment_mem : Q ∈ GroundingCut.G0
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
      (later_blockable : GroundingCut.IsBlockable
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut Q)
      (later_point_eq : GroundingCut.blockingPoint
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut Q =
          D.core.reduced.later)
      (later_point_mem_support : D.core.reduced.later ∈ Q.path.support)

/-- Eliminate the coarse blocker-to-finite owner pair using the exact
first selected departure at the blocker. -/
theorem SplitGroundedReachableBoundaryObstruction.boundaryFiniteOutcome
    (O : L.SplitGroundedReachableBoundaryObstruction
      (ReachableRecord (L := L) (hL := hL)
        (hground := hground) (S := S))) :
    SplitGroundedReachableBoundaryFiniteOutcome O := by
  cases O.firstBoundarySinkOutcome with
  | earlierControl D old hvalue hdeparture hlater =>
      exact .earlierControl D old hvalue hdeparture hlater
  | earlierBlocking D P hPG0 hblockable hpoint hsupport hdeparture hlater =>
      cases hlater with
      | finiteSource hfinite hcut =>
          rcases D.core.blockingFiniteTerminal_or_selectedDeparture
              P hPG0 hblockable hpoint hfinite hcut with
            hterminal | hselected
          · exact .blockingFiniteTerminal D hterminal
          · exact .blockingFiniteSelectedDeparture D P hPG0 hblockable
              hpoint hfinite hcut hselected
      | oldControl old hvalue =>
          exact .blockingToControl D P hPG0 hblockable hpoint hsupport
            hdeparture old hvalue
      | blocking Q hQG0 hQblockable hQpoint hQsupport =>
          exact .blockingToBlocking D P hPG0 hblockable hpoint hsupport
            hdeparture Q hQG0 hQblockable hQpoint hQsupport

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReachableBoundaryObstruction.boundaryFiniteOutcome
