/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantRootNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedSeparatorOutput

/-!
# Assertion 8.22 dispatcher on the descent-relevant frontier
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev RelevantDispatcherInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev RelevantDispatcherIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- Success is the genuine Assertion 8.22 output; failure is one point of
the final frontier with the strengthened relevant owner normal form. -/
theorem splitGroundedRelevantAssertion822Output_or_rootFailure
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (hTsub : T ⊆ L.splitGroundedRelevantBB hL.legal S.cut)
    (hTsep : Popular.IsSeparator Gamma T)
    (hcontrol : ∀ c : ControlRequest
        (RelevantDispatcherInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (RelevantDispatcherIndexed (L := L) (hL := hL)
              (hground := hground)) S K T) a c.1) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (RelevantDispatcherInput (L := L) (hL := hL)) S.cut) ∨
      ∃ t ∈ T, SplitGroundedRelevantBBRootFailureAt R T t := by
  rcases R.relevantFrontier_rootedAt_or_failure T hTsub hcontrol with
      hroot | hfailure
  · left
    exact L.splitGroundedAssertion822Output_of_frontierGeometry_withControls
      R T
        (hTsub.trans
          (L.splitGroundedRelevantBB_subset_legacyBB hL.legal S.cut))
        hTsep hroot
  · exact Or.inr hfailure

/-- The success side already yields an ambient hindrance. -/
theorem exists_hindrance_or_splitGroundedRelevantRootFailure
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (hTsub : T ⊆ L.splitGroundedRelevantBB hL.legal S.cut)
    (hTsep : Popular.IsSeparator Gamma T)
    (hcontrol : ∀ c : ControlRequest
        (RelevantDispatcherInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (RelevantDispatcherIndexed (L := L) (hL := hL)
              (hground := hground)) S K T) a c.1) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      ∃ t ∈ T, SplitGroundedRelevantBBRootFailureAt R T t := by
  rcases L.splitGroundedRelevantAssertion822Output_or_rootFailure
      R T hTsub hTsep hcontrol with houtput | hfailure
  · exact Or.inl
      (exists_hindrance_of_splitGroundedAssertion822Output houtput.some)
  · exact Or.inr hfailure

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedRelevantAssertion822Output_or_rootFailure
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_or_splitGroundedRelevantRootFailure
