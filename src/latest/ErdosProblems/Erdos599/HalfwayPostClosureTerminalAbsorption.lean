/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureCompressorAssignment
import ErdosProblems.Erdos599.HalfwayMovingBetaLimit

/-!
# Absorption of finite post-closure assignment terminals

At the captured later frontier, a limiting-reference component either did
not meet the old frontier, in which case its carrier belongs to the moving
reference difference already absorbed by the limit closure, or it met both
frontiers.  In the latter case the corresponding literal survivor interval
belongs to the finite interval reference.  Reference closure then shows
that this interval survives outside the closing set whenever its later
terminal does.  This contradicts the leaving endpoint of the simultaneous
assignment.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.Alternating
open _root_.Erdos599.CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

/-- Every displayed frontier vertex has a limiting-reference owner. -/
theorem exists_limitWarp_owner_of_mem_frontier
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Ladder.Stage (succ kappa)} {v : V}
    (hv : v ∈ C.ladder.frontier a) :
    ∃ p ∈ C.ladder.limitWarp, v ∈ p.support := by
  obtain ⟨q, hq, hqv⟩ :=
    Gamma.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      (C.legal.roofsSourceAtStages (Ladder.Stage.toExtended a)) hv
  obtain ⟨p, hp, hqp⟩ :=
    CardinalInduction.ControlledSlices.stagesEmbedInLimit_of_limitStages
      Gamma C.ladder C.legal.regular C.legal.limitStages a q hq.1
  exact ⟨p, hp, hqp.1 (Gamma.terminal_mem_support hqv)⟩

end ClubStageGeometry

namespace PostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ X0}

/-- A limiting component which meets both captured frontiers supplies the
literal canonical survivor interval ending at its later hit. -/
theorem exists_intervalReference_terminal_of_limitWarp_hits_frontiers
    (T : PostClosureIntervalTransaction C globalZ X0 z
      Rlimit.toDynamicMoving931GlobalClosure)
    {p : Gamma.DPath} (hp : p ∈ C.ladder.limitWarp)
    {x v : V}
    (hxOld : x ∈ C.ladder.frontier C.newStage) (hxp : x ∈ p.support)
    (hvNew : v ∈ C.ladder.frontier Rlimit.later.stage)
    (hvp : v ∈ p.support) :
    ∃ q ∈ T.intervalReference,
      q.terminal? = some v ∧ q.support ⊆ p.support := by
  obtain ⟨qa, hqa, hqaTerminal, hqaExt⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit
      C.legal hp hxOld hxp
  obtain ⟨qb, hqb, hqbTerminal, hqbExt⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit
      C.legal hp hvNew hvp
  obtain ⟨fa, rfl⟩ := ladderReference.finiteCharacter hqa
  obtain ⟨fb, rfl⟩ := ladderReference.finiteCharacter hqb
  have hfaFinish : fa.finish = x := Option.some.inj hqaTerminal
  have hfbFinish : fb.finish = v := Option.some.inj hqbTerminal
  have hgrows : Gamma.LadderGrows
      (C.ladder.warpAt C.newStage)
      (C.ladder.warpAt Rlimit.later.stage) :=
    DeferredStageInterval.warpAt_grows_of_le C.legal
      Rlimit.later.current_lt.le
  obtain ⟨r, hr, hfar⟩ := hgrows (.inl fa) hqa.1
  have hfaStart : fa.start = fb.start :=
    (Gamma.extends_initial hqaExt).trans
      (Gamma.extends_initial hqbExt).symm
  have hrEq : r = (Sum.inl fb : Gamma.DPath) := by
    apply DWeb.IsWarp.eq_of_mem_support
      (C.legal.warpStages
        (Ladder.Stage.toExtended Rlimit.later.stage)) hr hqb.1
    · exact Gamma.support_mono_of_extends hfar fa.start_mem_support
    · exact hfaStart ▸ fb.start_mem_support
  have hfab : Gamma.Extends (.inl fa : Gamma.DPath) (.inl fb) := by
    rw [hrEq] at hfar
    exact hfar
  have hxSurvivor : x ∈
      CardinalInduction.RegularSliceSurvivors.survivorSources
        Gamma C.ladder C.newStage Rlimit.later.stage :=
    ⟨hxOld, fa, fb, hqa, hqb, hfaFinish, hfab⟩
  have hxNotExceptional : x ∉
      Rlimit.toDynamicMoving931GlobalClosure.capturedGeometry.deferredOldStageExceptional := by
    rintro ⟨_hxOld, hxNotSurvivor⟩
    exact hxNotSurvivor hxSurvivor
  let a : ↑(Rlimit.toDynamicMoving931GlobalClosure.capturedGeometry.oldSlice \
      Rlimit.toDynamicMoving931GlobalClosure.capturedGeometry.deferredOldStageExceptional : Set V) :=
    ⟨x, hxOld, hxNotExceptional⟩
  let D := Rlimit.toDynamicMoving931GlobalClosure.capturedGeometry.deferredOldStageRealization
  have hleft : D.leftPrefix a = fa := by
    have hxLeft : x ∈ (D.leftPrefix a).support := by
      have hmem := (D.leftPrefix a).finish_mem_support
      rw [D.left_finish a] at hmem
      change x ∈ (D.leftPrefix a).support at hmem
      exact hmem
    have hxFa : x ∈ fa.support := by
      rw [← hfaFinish]
      exact fa.finish_mem_support
    apply Sum.inl.inj
    exact DWeb.IsWarp.eq_of_mem_support
      (C.legal.warpStages (Ladder.Stage.toExtended C.newStage))
      (D.left_mem a).1 hqa.1 hxLeft hxFa
  let hstart : Path.initial
      (.inl (D.toSegmentRealization.segment a) : Gamma.DPath) =
        (D.leftPrefix a).finish := by
    change (D.toSegmentRealization.segment a).start =
      (D.leftPrefix a).finish
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
    have hsupport := Path.support_appendFinite (D.leftPrefix a)
      (.inl (D.toSegmentRealization.segment a)) hstart hinter
    rw [happend] at hsupport
    exact hsupport.symm
  have hleftStartInRight :
      (D.leftPrefix a).start ∈ (D.rightPrefix a).support := by
    rw [← happendSupport]
    exact Or.inl (D.leftPrefix a).start_mem_support
  have hfaStartInRight : fa.start ∈ (D.rightPrefix a).support := by
    simpa only [hleft] using hleftStartInRight
  have hright : D.rightPrefix a = fb := by
    apply Sum.inl.inj
    apply DWeb.IsWarp.eq_of_mem_support
      (C.legal.warpStages
        (Ladder.Stage.toExtended Rlimit.later.stage))
      (D.right_mem a).1 hqb.1
    · exact hfaStartInRight
    · exact hfaStart ▸ fb.start_mem_support
  have hsegmentFinish :
      (D.toSegmentRealization.segment a).finish = v := by
    calc
      (D.toSegmentRealization.segment a).finish =
          (D.rightPrefix a).finish := (D.right_finish a).symm
      _ = fb.finish := congrArg FinitePath.finish hright
      _ = v := hfbFinish
  have hsegmentSupport :
      (D.toSegmentRealization.segment a).support ⊆ p.support := by
    intro y hy
    have hyRight : y ∈ (D.rightPrefix a).support := by
      rw [← happendSupport]
      exact Or.inr hy
    rw [hright] at hyRight
    exact Gamma.support_mono_of_extends hqbExt hyRight
  let q : Gamma.DPath := .inl (D.toSegmentRealization.segment a)
  have hqReference : q ∈ T.intervalReference := by
    change q ∈ SliceSegmentCore.liftStageFamily
      Rlimit.toDynamicMoving931GlobalClosure.capturedGeometry.ladder
      Rlimit.toDynamicMoving931GlobalClosure.capturedGeometry.oldStage
      Rlimit.toDynamicMoving931GlobalClosure.capturedGeometry.deferredOldStageOrdinaryFamily
    rw [Rlimit.toDynamicMoving931GlobalClosure.capturedGeometry.liftStageFamily_deferredOldStageOrdinaryFamily]
    exact ⟨a, rfl⟩
  refine ⟨q, hqReference, ?_, ?_⟩
  · change some (D.toSegmentRealization.segment a).finish = some v
    rw [hsegmentFinish]
  · exact hsegmentSupport

end PostClosureIntervalTransaction

namespace PostClosureCompressorAssignment

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ X0}
variable {T : PostClosureIntervalTransaction C globalZ X0 z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- Every finite endpoint produced by the actual post-closure compressor
assignment has already been absorbed by the moving limit closure. -/
theorem finite_terminal_mem_closedSet
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    {v : V}
    (hv : (A.assignment.produced.bracket.assignment.assigned s).terminal? =
      some v) :
    v ∈ Rlimit.closedSet := by
  by_contra hvNotClosed
  have hvHole :=
    (A.assignment.produced.bracket.assignment.finite_terminal_mem s hv).1
  have hvCut : v ∈
      CutSplit.terminalVertices
        (outsideCarrier T.interval.ambientInterval Rlimit.closedSet)
        (outsideFamilyEdges T.interval.ambientInterval Rlimit.closedSet)
        Rlimit.closedSet := by
    rw [← A.fractured.outside.terminalFrontier_eq]
    exact hvHole
  have hvRowTerminal : v ∈
      Gamma.terminalFrontier T.interval.ambientInterval :=
    cutTerminal_sdiff_subset_terminalFrontier
      T.interval.ambientInterval_linkage.isWarp ⟨hvCut, hvNotClosed⟩
  have hvNew : v ∈ C.ladder.frontier Rlimit.later.stage := by
    exact T.interval.ambientInterval_linkage.terminalFrontier_subset hvRowTerminal
  obtain ⟨p, hpLimit, hvp⟩ :=
    C.exists_limitWarp_owner_of_mem_frontier hvNew
  have hpNew : p ∈ C.limitReferenceAtFrontier Rlimit.later.stage :=
    ⟨hpLimit, v, hvp, hvNew⟩
  by_cases hpOld : p ∈ C.limitReferenceAtFrontier C.newStage
  · obtain ⟨x, hxp, hxOld⟩ := hpOld.2
    obtain ⟨q, hqReference, hqTerminal, hqSupport⟩ :=
      T.exists_intervalReference_terminal_of_limitWarp_hits_frontiers
        hpLimit hxOld hxp hvNew hvp
    have hpDisjoint : Disjoint p.support Rlimit.closedSet := by
      apply Set.disjoint_left.2
      intro w hwp hwClosed
      have hpSubset : p.support ⊆ Rlimit.closedSet :=
        Rlimit.reference_closed p hpLimit ⟨w, hwp, hwClosed⟩
      exact hvNotClosed (hpSubset hvp)
    have hqOutside : q ∈
        outsideReference T.intervalReference Rlimit.closedSet :=
      ⟨hqReference, hpDisjoint.mono_left hqSupport⟩
    have hvReference : v ∈ Gamma.vertexSet
        (outsideReference T.intervalReference Rlimit.closedSet) := by
      exact ⟨q, hqOutside,
        Gamma.terminal_mem_support hqTerminal⟩
    exact (A.assignment.produced.bracket.assignment.finite_terminal_mem
      s hv).2 hvReference
  · apply hvNotClosed
    apply Rlimit.difference_subset
    exact ⟨p, Or.inr ⟨hpNew, hpOld⟩, hvp⟩

end PostClosureCompressorAssignment

#print axioms ClubStageGeometry.exists_limitWarp_owner_of_mem_frontier
#print axioms
  PostClosureIntervalTransaction.exists_intervalReference_terminal_of_limitWarp_hits_frontiers
#print axioms PostClosureCompressorAssignment.finite_terminal_mem_closedSet

end Erdos599.Blueprint.LinkageBlueprint
