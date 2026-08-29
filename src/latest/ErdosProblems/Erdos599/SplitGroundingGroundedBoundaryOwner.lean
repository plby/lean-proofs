/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedPreStoppedOutcome

/-!
# Owner normal form for grounded split boundary obstructions

Every point of the raw grounding boundary has one of the three concrete
origins used by the construction: a finite old cut source, an old request
control, or the blocking point of a retained fragment.  Applying this
classification to both endpoints keeps an ordered boundary obstruction as
an explicit finite/control/blocking owner pair.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open PopularGroundingBridge GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev GroundedBoundaryInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

/-- The exact construction-side owner of one point of `BB`.  The old
request case is stored as its untagged control source, so it can be passed
directly to `oldRequestControl`; represented-edge requests cannot occur in
the old-vertex part of `BB`. -/
inductive SplitGroundedBBPointOwner (b : V) : Prop
  | finiteSource
      (source_mem : b ∈
        (GroundedBoundaryInput (L := L) (hL := hL)).finiteSource)
      (cut_mem : (PopularAuxiliary.Input.LambdaVertex.old b :
        (GroundedBoundaryInput (L := L) (hL := hL)).LV) ∈ S.cut)
  | oldControl
      (old : oldRequests
        (GroundedBoundaryInput (L := L) (hL := hL)) S.cut)
      (value_eq : old.1 = b)
  | blocking
      (P : (GroundedBoundaryInput (L := L) (hL := hL)).Fragment)
      (fragment_mem : P ∈ GroundingCut.G0
        (GroundedBoundaryInput (L := L) (hL := hL)) S.cut)
      (blockable : GroundingCut.IsBlockable
        (GroundedBoundaryInput (L := L) (hL := hL)) S.cut P)
      (point_eq : GroundingCut.blockingPoint
        (GroundedBoundaryInput (L := L) (hL := hL)) S.cut P = b)
      (point_mem_support : b ∈ P.path.support)

/-- Classify a raw boundary point by its actual construction-side owner. -/
theorem splitGroundedBBPointOwner_of_mem {b : V}
    (hb : b ∈ GroundingCut.BB
      (GroundedBoundaryInput (L := L) (hL := hL)) S.cut) :
    SplitGroundedBBPointOwner (L := L) (hL := hL) (hground := hground)
      (S := S) b := by
  rcases GroundingBBGeometry.mem_BB_finiteSourceWithCut_or_oldRequestExit_or_blockingPoint
      hb with
    ⟨hfinite, hcut⟩ | ⟨r, hrAux, hrExit⟩ |
      ⟨P, hPG0, hPblockable, hPt, htSupport⟩
  · exact .finiteSource hfinite hcut
  · cases r with
    | inl old =>
        exact .oldControl old (by simpa only [requestExit] using hrExit)
    | inr edge => cases hrAux
  · exact .blocking P hPG0 hPblockable hPt htSupport

/-- An ordered pair of distinct boundary points together with the exact
finite/control/blocking owner of each endpoint. -/
structure SplitGroundedPreStoppedBoundaryOwnerPair
    (R : L.SplitGroundedUnusedRecord hL hground S K) where
  obstruction : L.SplitGroundedPreStoppedBoundaryObstruction R
  earlier_owner : SplitGroundedBBPointOwner
    (L := L) (hL := hL) (hground := hground) (S := S)
      obstruction.earlier
  later_owner : SplitGroundedBBPointOwner
    (L := L) (hL := hL) (hground := hground) (S := S)
      obstruction.later

/-- Normalize both endpoints of an ordered boundary obstruction without
discarding its distinctness or its pre-stopped reachability witness. -/
def SplitGroundedPreStoppedBoundaryObstruction.ownerPair
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (O : L.SplitGroundedPreStoppedBoundaryObstruction R) :
    SplitGroundedPreStoppedBoundaryOwnerPair R :=
  { obstruction := O
    earlier_owner := L.splitGroundedBBPointOwner_of_mem O.earlier_mem
    later_owner := L.splitGroundedBBPointOwner_of_mem O.later_mem }

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedPreStoppedBoundaryObstruction.ownerPair
