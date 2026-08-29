/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayDeferredOldStageComplement

/-!
# Deferred survivor intervals at an explicit old stage

Only the later stage must belong to the avoiding club. In particular these
are the actual zero-to-club intervals, without an assumption that zero is
a club member. All paths and their ambient lifts are the existing literal
survivor segments.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open DeferredStageInterval SliceCandidate

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable (C : ClubStageGeometry Gamma Y kappa (succ kappa))

def stageExceptional (a b : Stage (succ kappa)) : Set V :=
  RegularSliceSurvivors.nonsurvivorSources Gamma C.ladder a b

theorem mk_stageExceptional_le {a b : Stage (succ kappa)}
    (hab : a ≤ b) (hb : b ∈ C.club) : #(C.stageExceptional a b) ≤ kappa := by
  have hle : #(C.stageExceptional a b) ≤
      #(Gamma.inessentialPaths (C.ladder.warpAt b)) :=
    RegularSliceSurvivors.mk_nonsurvivorSources_le_inessential
      C.legal.roofsSourceAtStages C.legal.warpStages
      (DeferredStageInterval.warpAt_grows_of_le C.legal hab)
  apply lt_succ_iff.mp
  apply hle.trans_lt
  apply DWeb.KappaLadder.Deferred.mk_inessentialWarpAt_lt_of_not_mem_phi C.legal b
  intro hbPhi
  exact Set.disjoint_left.mp C.club_avoids_phi hb hbPhi

def ordinaryStageRealization {a b : Stage (succ kappa)} (hab : a ≤ b) :
    StageIntervalRealization C.ladder a b (C.ladder.frontier a \ C.stageExceptional a b) :=
  RegularSliceSurvivors.stageIntervalRealizationOfSubset_of_geometry
    (by
      rintro x ⟨hx, hnot⟩
      by_contra hmiss
      exact hnot ⟨hx, hmiss⟩)
    C.legal.roofsSourceAtStages C.legal.warpStages
    (DeferredStageInterval.warpAt_grows_of_le C.legal hab)

def ordinaryStageFamily {a b : Stage (succ kappa)} (hab : a ≤ b) :
    Set (C.ladder.stageWeb a).DPath :=
  StageIntervalRealization.stageFamily (C.ordinaryStageRealization hab) C.legal hab

theorem ordinaryStageFamily_isLinkageBetween {a b : Stage (succ kappa)} (hab : a ≤ b) :
    IsLinkageBetween (C.ladder.stageWeb a)
      (C.ladder.frontier a \ C.stageExceptional a b) (C.ladder.frontier b)
      (C.ordinaryStageFamily hab) :=
  StageIntervalRealization.stageFamily_isLinkageBetween
    (C.ordinaryStageRealization hab) C.legal hab

theorem ordinaryStageFamily_meetsOnlyAtTerminal {a b : Stage (succ kappa)} (hab : a ≤ b) :
    SliceSpliceSource.MeetsOnlyAtTerminal (C.ladder.stageWeb a)
      (C.ordinaryStageFamily hab) (C.ladder.frontier b) :=
  StageIntervalRealization.stageFamily_meetsOnlyAtTerminal
    (C.ordinaryStageRealization hab) C.legal hab

@[simp] theorem liftStageFamily_ordinaryStageFamily {a b : Stage (succ kappa)} (hab : a ≤ b) :
    SliceSegmentCore.liftStageFamily C.ladder a (C.ordinaryStageFamily hab) =
      SliceSegmentCore.segmentFamily (C.ordinaryStageRealization hab).toSegmentRealization :=
  StageIntervalRealization.liftStageFamily_stageFamily
    (C.ordinaryStageRealization hab) C.legal hab

#print axioms mk_stageExceptional_le
#print axioms ordinaryStageFamily_isLinkageBetween
#print axioms liftStageFamily_ordinaryStageFamily

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
