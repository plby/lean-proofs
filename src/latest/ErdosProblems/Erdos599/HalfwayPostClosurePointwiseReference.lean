/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureTerminalAbsorption
import ErdosProblems.Erdos599.HalfwayPostClosureOldRoofIncidence
import ErdosProblems.Erdos599.HalfwayMovingInessentialAbsorption

/-!
# Pointwise containment in the captured interval reference

The terminal-only survivor theorem is strengthened at an actual later-row
contact.  If a limiting-reference owner meets both captured frontiers and a
vertex of the ambient interval row, the canonical interval selected on that
owner contains that vertex.  The proof uses the literal prefix-append
identity of the stage interval realization.  It does not identify the
ambient row with the reference row.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

/-- One member of the limiting warp meets a stage frontier in at most one
vertex.  Each hit is the terminal of an essential stage prefix, and the two
prefixes have the same initial vertex. -/
theorem limitWarp_frontier_hit_unique
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Ladder.Stage (succ kappa)} {p : Gamma.DPath}
    (hp : p ∈ C.ladder.limitWarp) {x y : V}
    (hx : x ∈ C.ladder.frontier a) (hxp : x ∈ p.support)
    (hy : y ∈ C.ladder.frontier a) (hyp : y ∈ p.support) :
    x = y := by
  obtain ⟨q, hq, hqx, hqp⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit
      C.legal hp hx hxp
  obtain ⟨r, hr, hry, hrp⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit
      C.legal hp hy hyp
  have hqr : q = r := by
    apply DWeb.IsWarp.eq_of_initial_eq Gamma
      (ladderReference.isWarp C.legal) hq hr
    exact (Gamma.extends_initial hqp).trans
      (Gamma.extends_initial hrp).symm
  rw [hqr] at hqx
  exact Option.some.inj (hqx.symm.trans hry)

end ClubStageGeometry

namespace PostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}

/-- A contact of one global owner with the actual ambient interval row lies
on the literal canonical reference interval of that owner. -/
theorem exists_intervalReference_containing_of_limitWarp_hits_frontiers
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {p : Gamma.DPath} (hp : p ∈ C.ladder.limitWarp)
    {x v w : V}
    (hxOld : x ∈ C.ladder.frontier C.newStage) (hxp : x ∈ p.support)
    (hvNew : v ∈ C.ladder.frontier Rlimit.later.stage)
    (hvp : v ∈ p.support) (hwp : w ∈ p.support)
    (hwRow : w ∈ Gamma.vertexSet T.interval.ambientInterval) :
    ∃ q ∈ T.intervalReference,
      w ∈ q.support ∧ q.terminal? = some v ∧ q.support ⊆ p.support := by
  obtain ⟨q, hq, hqTerminal, hqSupport⟩ :=
    T.exists_intervalReference_terminal_of_limitWarp_hits_frontiers
      hp hxOld hxp hvNew hvp
  let qs : T.intervalReference := ⟨q, hq⟩
  let D := Rlimit.capturedGeometry.deferredOldStageRealization
  let a := T.intervalReferenceSource qs
  have hqEq : q =
      (Sum.inl (D.toSegmentRealization.segment a) : Gamma.DPath) := by
    exact T.intervalReference_eq_segment_source qs
  have hqInitialOld : q.initial ∈ C.ladder.frontier C.newStage := by
    have hinit : q.initial ∈ Gamma.initialSet T.intervalReference :=
      ⟨q, hq, rfl⟩
    rw [T.intervalReference_isLinkageBetween.initialSet_eq] at hinit
    simpa only [DynamicMoving931GlobalClosure.capturedGeometry_oldSlice]
      using hinit.1
  have hqInitialP : q.initial ∈ p.support :=
    hqSupport q.initial_mem_support
  have hqInitial : q.initial = x :=
    C.limitWarp_frontier_hit_unique hp hqInitialOld hqInitialP hxOld hxp
  have hsegmentFinish : (D.toSegmentRealization.segment a).finish = v := by
    rw [hqEq] at hqTerminal
    exact Option.some.inj hqTerminal
  have hvRight : v ∈ (D.rightPrefix a).support := by
    rw [← hsegmentFinish, ← D.right_finish a]
    exact (D.rightPrefix a).finish_mem_support
  have hrightExt : Gamma.Extends
      (.inl (D.rightPrefix a) : Gamma.DPath) p := by
    apply C.legal.extends_limitWarp_of_stage_intersects
      (D.right_mem a).1 hp
    exact ⟨v, hvRight, hvp⟩
  have hwLaterRoof : w ∈ Gamma.roof
      (C.ladder.frontier Rlimit.later.stage) := by
    obtain ⟨r, hr, hwr⟩ := hwRow
    exact T.interval.ambientInterval_in_outerRoof r hr hwr
  have hwRight : w ∈ (D.rightPrefix a).support :=
    DWeb.KappaLadder.Deferred.limitComponent_support_inter_roof_subset_prefix
      C.legal Rlimit.later.stage hp (D.right_mem a).1 hrightExt
        ⟨hwp, hwLaterRoof⟩
  let hstart : Path.initial
      (.inl (D.toSegmentRealization.segment a) : Gamma.DPath) =
        (D.leftPrefix a).finish := by
    exact (D.toSegmentRealization.segment_start a).trans
      (D.left_finish a).symm
  let hinter : (D.leftPrefix a).support ∩
      (D.toSegmentRealization.segment a).support ⊆
        {(D.leftPrefix a).finish} :=
    (D.prefix_inter a).subset
  have happend : Path.appendFinite (D.leftPrefix a)
      (.inl (D.toSegmentRealization.segment a)) hstart hinter =
        (.inl (D.rightPrefix a) : Gamma.DPath) := by
    convert D.append_eq a
  have happendSupport :
      (D.leftPrefix a).support ∪
          (D.toSegmentRealization.segment a).support =
        (D.rightPrefix a).support := by
    have hs := Path.support_appendFinite (D.leftPrefix a)
      (.inl (D.toSegmentRealization.segment a)) hstart hinter
    rw [happend] at hs
    exact hs.symm
  have hwUnion : w ∈ (D.leftPrefix a).support ∪
      (D.toSegmentRealization.segment a).support := by
    rw [happendSupport]
    exact hwRight
  have hwQ : w ∈ q.support := by
    rcases hwUnion with hwLeft | hwSegment
    · have hwOldRoof : w ∈ Gamma.roof C.newSlice := by
        have hwRaw :=
          DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier
            C.legal C.newStage
              ⟨Sum.inl (D.leftPrefix a), (D.left_mem a).1, hwLeft⟩
        change w ∈ Gamma.roof (C.ladder.frontier C.newStage)
        rw [C.ladder.frontier_eq_essential_terminalFrontier
          C.legal.roofsSourceAtStages, Gamma.roof_essential]
        exact hwRaw
      have hwOld : w ∈ C.ladder.frontier C.newStage := by
        have hwCaptured : w ∈ Rlimit.capturedGeometry.oldSlice := by
          rw [← T.interval.ambientInterval_vertexSet_inter_oldRoof]
          exact ⟨hwRow, by
            simpa only [DynamicMoving931GlobalClosure.capturedGeometry_oldSlice]
              using hwOldRoof⟩
        simpa only [DynamicMoving931GlobalClosure.capturedGeometry_oldSlice]
          using hwCaptured
      have hwx : w = x :=
        C.limitWarp_frontier_hit_unique hp hwOld hwp hxOld hxp
      rw [hwx, ← hqInitial]
      exact q.initial_mem_support
    · rw [hqEq]
      exact hwSegment
  exact ⟨q, hq, hwQ, hqTerminal, hqSupport⟩

end PostClosureIntervalTransaction

#print axioms ClubStageGeometry.limitWarp_frontier_hit_unique
#print axioms
  PostClosureIntervalTransaction.exists_intervalReference_containing_of_limitWarp_hits_frontiers

end Erdos599.Blueprint.LinkageBlueprint
