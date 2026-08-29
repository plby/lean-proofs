/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedPreStoppedOutcome

/-!
# Root-obstruction normalization after grounded controls are rooted

Once all old request controls are rooted, the `CV` part of `BB` cannot be a
root obstruction.  The exact remaining cases are a finite old cut source or
a blockable fragment, with the latter already reduced to the source-faithful
blocking outcome.
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

private abbrev GroundedRootOutcomeInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev GroundedRootOutcomeIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- Concrete root-failure alternatives after the control vertices have
already been rooted. -/
inductive SplitGroundedRootFailureAfterControls
    (R : L.SplitGroundedUnusedRecord hL hground S K) : Prop
  | finiteSource
      (b : V)
      (source_mem : b ∈
        (GroundedRootOutcomeInput (L := L) (hL := hL)).finiteSource)
      (cut_mem : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootOutcomeIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a b)
      (outcome : SplitGroundedUnusedRecord.SplitGroundedFiniteSourceRootFailureOutcome
        R b source_mem)
  | blocking
      (P : (GroundedRootOutcomeInput (L := L) (hL := hL)).Fragment)
      (fragment_mem : P ∈ GroundingCut.G0
        (GroundedRootOutcomeInput (L := L) (hL := hL)) S.cut)
      (outcome : SplitGroundedUnusedRecord.SplitGroundedBlockingRootFailureOutcome
        R P)

/-- Normalize an actual unrooted `BB` point after all controls have been
rooted.  The full blocking normal form remains in `outcome`. -/
theorem SplitGroundedPreStoppedRootObstruction.failureAfterControls
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (O : L.SplitGroundedPreStoppedRootObstruction R)
    (hcontrol : ∀ c : ControlRequest
        (GroundedRootOutcomeInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedRootOutcomeIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a c.1) :
    L.SplitGroundedRootFailureAfterControls R := by
  rcases GroundingBBGeometry.mem_BB_finiteSourceWithCut_or_oldRequestExit_or_blockingPoint
      O.boundary_mem with
    ⟨hfinite, hcut⟩ | ⟨r, hrAux, hrExit⟩ |
      ⟨P, hPG0, _hblockable, hPt, _htSupport⟩
  · have houtcome :=
      (R.finiteSourceRootFailureOutcome hfinite hcut O.not_rooted hcontrol).some
    exact .finiteSource O.boundary hfinite hcut O.not_rooted houtcome
  · cases r with
    | inl old =>
        have hold : old.1 = O.boundary := by
          simpa only [requestExit] using hrExit
        apply False.elim
        apply O.not_rooted
        simpa only [oldRequestControl_val, hold] using
          hcontrol (oldRequestControl old)
    | inr edge => cases hrAux
  · have houtcome :=
      R.blockingPointRootFailureOutcome P hPG0
        (by simpa only [hPt] using O.not_rooted) hcontrol
    exact .blocking P hPG0 houtcome

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedPreStoppedRootObstruction.failureAfterControls
