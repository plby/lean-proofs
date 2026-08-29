/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReducedCut
import ErdosProblems.Erdos599.GroundingBBGeometry

/-!
# Owner normal form for the source-correct split grounding boundary

The coarse boundary-owner normal form forgets whether a blocking fragment
survives the `H_empty` deletion.  This module classifies a point of
`splitGroundedBB` directly, retaining membership in the corrected reduced
blocking domain.
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

private abbrev ReducedBoundaryInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

/-- The exact construction-side owner of one point of the source-correct
boundary.  In the blocking case the fragment is retained in the reduced
domain, not merely in the legacy coarse domain. -/
inductive SplitGroundedReducedBBPointOwner (b : V) : Prop
  | finiteSource
      (source_mem : b ∈
        (ReducedBoundaryInput (L := L) (hL := hL)).finiteSource)
      (cut_mem : (PopularAuxiliary.Input.LambdaVertex.old b :
        (ReducedBoundaryInput (L := L) (hL := hL)).LV) ∈ S.cut)
  | oldControl
      (old : oldRequests
        (ReducedBoundaryInput (L := L) (hL := hL)) S.cut)
      (value_eq : old.1 = b)
  | blocking
      (P : (ReducedBoundaryInput (L := L) (hL := hL)).Fragment)
      (fragment_mem : P ∈ L.splitGroundedG0 hL.legal S.cut)
      (point_eq : GroundingCut.blockingPoint
        (ReducedBoundaryInput (L := L) (hL := hL)) S.cut P = b)
      (point_mem_support : b ∈ P.path.support)

/-- Classify a corrected boundary point without forgetting that a blocking
owner survives `H_empty`. -/
theorem splitGroundedReducedBBPointOwner_of_mem {b : V}
    (hb : b ∈ L.splitGroundedBB hL.legal S.cut) :
    SplitGroundedReducedBBPointOwner
      (L := L) (hL := hL) (hground := hground) (S := S) b := by
  rcases hb with hbCV | hbBL
  · rcases GroundingBBGeometry.mem_CV_finiteSource_or_oldRequestExit hbCV with
      hfinite | ⟨r, hrAux, hrExit⟩
    · exact .finiteSource hfinite (GroundingCut.mem_CV.mp hbCV)
    · cases r with
      | inl old =>
          exact .oldControl old (by simpa only [requestExit] using hrExit)
      | inr edge => cases hrAux
  · obtain ⟨P, hP, hpoint⟩ := hbBL
    subst b
    exact .blocking P hP rfl
      (GroundingCut.blockingPoint_mem_support
        (ReducedBoundaryInput (L := L) (hL := hL)) S.cut P hP.2)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedReducedBBPointOwner_of_mem
