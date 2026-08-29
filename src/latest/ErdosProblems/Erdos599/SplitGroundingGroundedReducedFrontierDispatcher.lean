/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReducedRootNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedSeparatorOutput

/-!
# Assertion 8.22 dispatcher on a source-correct final frontier

For a separating frontier inside `splitGroundedBB`, the `T`-stopped root
normalizer either supplies every root required by the genuine Assertion 8.22
compiler or exposes one concrete reduced finite/blocking failure.  No
pre-stopped-to-stopped reachability inference is used.
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

private abbrev ReducedDispatcherInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev ReducedDispatcherIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- Exact final-frontier dispatcher: success is the genuine Assertion 8.22
output; failure is one point of the chosen frontier with its reduced owner
normal form. -/
theorem splitGroundedReducedAssertion822Output_or_rootFailure
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (hTsub : T ⊆ L.splitGroundedBB hL.legal S.cut)
    (hTsep : Popular.IsSeparator Gamma T)
    (hcontrol : ∀ c : ControlRequest
        (ReducedDispatcherInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (ReducedDispatcherIndexed (L := L) (hL := hL)
              (hground := hground)) S K T) a c.1) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (ReducedDispatcherInput (L := L) (hL := hL)) S.cut) ∨
      ∃ t ∈ T,
        R.SplitGroundedReducedBBRootFailureAt T t := by
  rcases R.reducedFrontier_rootedAt_or_failure T hTsub hcontrol with
      hroot | hfailure
  · left
    exact L.splitGroundedAssertion822Output_of_frontierGeometry_withControls
      R T
        (hTsub.trans (L.splitGroundedBB_subset_legacyBB hL.legal S.cut))
        hTsep hroot
  · exact Or.inr hfailure

/-- On the success side the dispatcher already yields the ambient
hindrance; the other side retains the same concrete root failure. -/
theorem exists_hindrance_or_splitGroundedReducedRootFailure
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (hTsub : T ⊆ L.splitGroundedBB hL.legal S.cut)
    (hTsep : Popular.IsSeparator Gamma T)
    (hcontrol : ∀ c : ControlRequest
        (ReducedDispatcherInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (ReducedDispatcherIndexed (L := L) (hL := hL)
              (hground := hground)) S K T) a c.1) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      ∃ t ∈ T,
        R.SplitGroundedReducedBBRootFailureAt T t := by
  rcases L.splitGroundedReducedAssertion822Output_or_rootFailure
      R T hTsub hTsep hcontrol with houtput | hfailure
  · exact Or.inl
      (exists_hindrance_of_splitGroundedAssertion822Output houtput.some)
  · exact Or.inr hfailure

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedReducedAssertion822Output_or_rootFailure
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_or_splitGroundedReducedRootFailure
