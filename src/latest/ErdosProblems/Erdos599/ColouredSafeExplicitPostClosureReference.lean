/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayExplicitPostClosureTransaction
import ErdosProblems.Erdos599.HalfwayNativeReferenceIncidence
import ErdosProblems.Erdos599.HalfwayPostClosurePointwiseReference

/-!
# Explicit-stage interval reference and limiting owners

The canonical finite survivor intervals selected over a native moving
closure, with its actual old index, embed memberwise in the ladder's
limiting warp. Contacts with the
actual completed interval row are pointwise visible in the corresponding
local interval.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.Alternating
open _root_.Erdos599.CardinalInduction
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace StagePostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {alpha : Stage (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

/-- The source coordinate of one literal native captured interval. -/
noncomputable def intervalReferenceSource
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (q : T.intervalReference) :
    ↑((C.ladder.frontier alpha) \
      (C.stageExceptional alpha R.later.stage) : Set V) := by
  refine ⟨q.1.initial, ?_⟩
  rw [← T.intervalReference_isLinkageBetween.initialSet_eq]
  exact ⟨q.1, q.2, rfl⟩

theorem intervalReference_eq_segment_source
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (q : T.intervalReference) :
    q.1 =
      (Sum.inl
        (T.intervalRealization.toSegmentRealization.segment
          (T.intervalReferenceSource q)) : Gamma.DPath) := by
  have hq := q.2
  change q.1 ∈ SliceSegmentCore.liftStageFamily
    C.ladder alpha
      (C.ordinaryStageFamily T.current_lt.le) at hq
  rw [(C.liftStageFamily_ordinaryStageFamily T.current_lt.le)] at hq
  obtain ⟨a, hqa⟩ := hq
  have ha : a = T.intervalReferenceSource q := by
    apply Subtype.ext
    change a.1 = q.1.initial
    exact
      (T.intervalRealization.toSegmentRealization.segment_start
        a).symm.trans (congrArg DirectedPath.Path.initial hqa)
  rw [← ha]
  exact hqa.symm

theorem exists_limitWarp_owner_for_intervalSource
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (a : ↑((C.ladder.frontier alpha) \
      (C.stageExceptional alpha R.later.stage) : Set V)) :
    ∃ p ∈ C.ladder.limitWarp,
      Gamma.Extends
        (T.intervalRealization.toSegmentRealization.carrier a)
        p := by
  have hlimit : Order.IsSuccLimit (succ kappa).ord :=
    Cardinal.isSuccLimit_ord C.legal.regular.aleph0_le
  exact C.legal.limitStages.grows_to_limit
    (Ladder.finalStage (succ kappa)) hlimit
    ⟨R.later.stage.1,
      R.later.stage.2⟩
    (T.intervalRealization.toSegmentRealization.carrier a)
    (T.intervalRealization.toSegmentRealization.carrier_mem a)

noncomputable def limitOwnerForIntervalSource
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (a : ↑((C.ladder.frontier alpha) \
      (C.stageExceptional alpha R.later.stage) : Set V)) :
    Gamma.DPath :=
  Classical.choose (T.exists_limitWarp_owner_for_intervalSource a)

theorem limitOwnerForIntervalSource_mem
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (a : ↑((C.ladder.frontier alpha) \
      (C.stageExceptional alpha R.later.stage) : Set V)) :
    T.limitOwnerForIntervalSource a ∈ C.ladder.limitWarp :=
  (Classical.choose_spec
    (T.exists_limitWarp_owner_for_intervalSource a)).1

theorem carrier_extends_limitOwnerForIntervalSource
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (a : ↑((C.ladder.frontier alpha) \
      (C.stageExceptional alpha R.later.stage) : Set V)) :
    Gamma.Extends
      (T.intervalRealization.toSegmentRealization.carrier a)
      (T.limitOwnerForIntervalSource a) :=
  (Classical.choose_spec
    (T.exists_limitWarp_owner_for_intervalSource a)).2

noncomputable def intervalReferenceOwner
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (q : T.intervalReference) : Gamma.DPath :=
  T.limitOwnerForIntervalSource (T.intervalReferenceSource q)

theorem intervalReferenceOwner_mem
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (q : T.intervalReference) :
    T.intervalReferenceOwner q ∈ C.ladder.limitWarp :=
  T.limitOwnerForIntervalSource_mem (T.intervalReferenceSource q)

theorem intervalReference_subpath_owner
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (q : T.intervalReference) :
    q.1.IsSubpathOf (T.intervalReferenceOwner q) := by
  rw [T.intervalReference_eq_segment_source q]
  exact ⟨
    (T.intervalRealization.toSegmentRealization.segment_subpath
      (T.intervalReferenceSource q)).1.trans
        (Gamma.support_mono_of_extends
          (T.carrier_extends_limitOwnerForIntervalSource
            (T.intervalReferenceSource q))),
    (T.intervalRealization.toSegmentRealization.segment_subpath
      (T.intervalReferenceSource q)).2.trans
        (DirectedPath.Path.edgeSet_mono_of_extends
          (T.carrier_extends_limitOwnerForIntervalSource
            (T.intervalReferenceSource q)))⟩

theorem intervalReferenceOwner_injective
    (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    Function.Injective T.intervalReferenceOwner := by
  intro q r howner
  let a := T.intervalReferenceSource q
  let b := T.intervalReferenceSource r
  have hcarrier :
      T.intervalRealization.toSegmentRealization.carrier a =
        T.intervalRealization.toSegmentRealization.carrier b := by
    apply DWeb.IsWarp.eq_of_initial_eq Gamma
      (C.legal.warpStages
        (Ladder.Stage.toExtended R.later.stage))
      (T.intervalRealization.toSegmentRealization.carrier_mem a)
      (T.intervalRealization.toSegmentRealization.carrier_mem b)
    calc
      (T.intervalRealization.toSegmentRealization.carrier a).initial =
          (T.limitOwnerForIntervalSource a).initial :=
        Gamma.extends_initial (T.carrier_extends_limitOwnerForIntervalSource a)
      _ = (T.limitOwnerForIntervalSource b).initial := by
        exact congrArg DirectedPath.Path.initial howner
      _ =
          (T.intervalRealization.toSegmentRealization.carrier b).initial :=
        (Gamma.extends_initial
          (T.carrier_extends_limitOwnerForIntervalSource b)).symm
  have hab : a = b :=
    T.intervalRealization.toSegmentRealization.carrier_injective
      hcarrier
  have hsources : T.intervalReferenceSource q =
      T.intervalReferenceSource r := by
    simpa only [a, b] using hab
  apply Subtype.ext
  rw [T.intervalReference_eq_segment_source q,
    T.intervalReference_eq_segment_source r, hsources]

/-- The native captured interval reference embeds injectively into the
limiting warp. -/
noncomputable def intervalGlobalReferenceEmbedding
    (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    _root_.Erdos599.Blueprint.ReferenceSubpathEmbedding Gamma
      T.intervalReference C.ladder.limitWarp where
  owner q := ⟨T.intervalReferenceOwner q, T.intervalReferenceOwner_mem q⟩
  owner_injective := by
    intro q r hqr
    apply T.intervalReferenceOwner_injective
    exact congrArg Subtype.val hqr
  support_subset q := (T.intervalReference_subpath_owner q).1
  edgeSet_subset q := (T.intervalReference_subpath_owner q).2
  global_isWarp := C.legal.warpStages (Ladder.finalStage (succ kappa))

/-- Restrict the native interval embedding to reference members disjoint
from the closed carrier. -/
noncomputable def outsideIntervalGlobalReferenceEmbedding
    (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    _root_.Erdos599.Blueprint.ReferenceSubpathEmbedding Gamma
      (outsideReference T.intervalReference R.closedSet)
      C.ladder.limitWarp where
  owner q := T.intervalGlobalReferenceEmbedding.owner ⟨q.1, q.2.1⟩
  owner_injective := by
    intro q r hqr
    apply Subtype.ext
    have hfull : (⟨q.1, q.2.1⟩ : T.intervalReference) =
        ⟨r.1, r.2.1⟩ :=
      T.intervalGlobalReferenceEmbedding.owner_injective hqr
    exact congrArg (fun p : T.intervalReference ↦ p.1) hfull
  support_subset q :=
    T.intervalGlobalReferenceEmbedding.support_subset ⟨q.1, q.2.1⟩
  edgeSet_subset q :=
    T.intervalGlobalReferenceEmbedding.edgeSet_subset ⟨q.1, q.2.1⟩
  global_isWarp := T.intervalGlobalReferenceEmbedding.global_isWarp

/-- A limiting component meeting both native captured frontiers supplies
the literal survivor interval ending at its later hit. -/
theorem exists_intervalReference_terminal_of_limitWarp_hits_frontiers
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    {p : Gamma.DPath} (hp : p ∈ C.ladder.limitWarp)
    {x v : V}
    (hxOld : x ∈ C.ladder.frontier alpha) (hxp : x ∈ p.support)
    (hvNew : v ∈ C.ladder.frontier R.later.stage)
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
      (C.ladder.warpAt alpha)
      (C.ladder.warpAt R.later.stage) :=
    DeferredStageInterval.warpAt_grows_of_le C.legal T.current_lt.le
  obtain ⟨r, hr, hfar⟩ := hgrows (.inl fa) hqa.1
  have hfaStart : fa.start = fb.start :=
    (Gamma.extends_initial hqaExt).trans
      (Gamma.extends_initial hqbExt).symm
  have hrEq : r = (Sum.inl fb : Gamma.DPath) := by
    apply DWeb.IsWarp.eq_of_mem_support
      (C.legal.warpStages (Ladder.Stage.toExtended R.later.stage)) hr hqb.1
    · exact Gamma.support_mono_of_extends hfar fa.start_mem_support
    · exact hfaStart ▸ fb.start_mem_support
  have hfab : Gamma.Extends (.inl fa : Gamma.DPath) (.inl fb) := by
    rw [hrEq] at hfar
    exact hfar
  have hxSurvivor : x ∈
      CardinalInduction.RegularSliceSurvivors.survivorSources
        Gamma C.ladder alpha R.later.stage :=
    ⟨hxOld, fa, fb, hqa, hqb, hfaFinish, hfab⟩
  have hxNotExceptional : x ∉
      (C.stageExceptional alpha R.later.stage) := by
    rintro ⟨_hxOld, hxNotSurvivor⟩
    exact hxNotSurvivor hxSurvivor
  let a : ↑((C.ladder.frontier alpha) \
      (C.stageExceptional alpha R.later.stage) : Set V) :=
    ⟨x, hxOld, hxNotExceptional⟩
  let D := T.intervalRealization
  have hleft : D.leftPrefix a = fa := by
    have hxLeft : x ∈ (D.leftPrefix a).support := by
      have hmem := (D.leftPrefix a).finish_mem_support
      rw [D.left_finish a] at hmem
      exact hmem
    have hxFa : x ∈ fa.support := by
      rw [← hfaFinish]
      exact fa.finish_mem_support
    apply Sum.inl.inj
    exact DWeb.IsWarp.eq_of_mem_support
      (C.legal.warpStages (Ladder.Stage.toExtended alpha))
      (D.left_mem a).1 hqa.1 hxLeft hxFa
  let hstart : Path.initial
      (.inl (D.toSegmentRealization.segment a) : Gamma.DPath) =
        (D.leftPrefix a).finish := by
    exact (D.toSegmentRealization.segment_start a).trans
      (D.left_finish a).symm
  let hinter : (D.leftPrefix a).support ∩
      (D.toSegmentRealization.segment a).support ⊆
        {(D.leftPrefix a).finish} := (D.prefix_inter a).subset
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
  have hleftStartInRight :
      (D.leftPrefix a).start ∈ (D.rightPrefix a).support := by
    rw [← happendSupport]
    exact Or.inl (D.leftPrefix a).start_mem_support
  have hfaStartInRight : fa.start ∈ (D.rightPrefix a).support := by
    simpa only [hleft] using hleftStartInRight
  have hright : D.rightPrefix a = fb := by
    apply Sum.inl.inj
    apply DWeb.IsWarp.eq_of_mem_support
      (C.legal.warpStages (Ladder.Stage.toExtended R.later.stage))
      (D.right_mem a).1 hqb.1
    · exact hfaStartInRight
    · exact hfaStart ▸ fb.start_mem_support
  have hsegmentFinish : (D.toSegmentRealization.segment a).finish = v := by
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
      C.ladder
      alpha
      (C.ordinaryStageFamily T.current_lt.le)
    rw [(C.liftStageFamily_ordinaryStageFamily T.current_lt.le)]
    exact ⟨a, rfl⟩
  refine ⟨q, hqReference, ?_, hsegmentSupport⟩
  change some (D.toSegmentRealization.segment a).finish = some v
  rw [hsegmentFinish]

/-- Pointwise form: a contact with the completed row is contained in the
literal interval of its limiting owner. -/
theorem exists_intervalReference_containing_of_limitWarp_hits_frontiers
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    {p : Gamma.DPath} (hp : p ∈ C.ladder.limitWarp)
    {x v w : V}
    (hxOld : x ∈ C.ladder.frontier alpha) (hxp : x ∈ p.support)
    (hvNew : v ∈ C.ladder.frontier R.later.stage)
    (hvp : v ∈ p.support) (hwp : w ∈ p.support)
    (hwRow : w ∈ Gamma.vertexSet T.interval.ambientInterval) :
    ∃ q ∈ T.intervalReference,
      w ∈ q.support ∧ q.terminal? = some v ∧ q.support ⊆ p.support := by
  obtain ⟨q, hq, hqTerminal, hqSupport⟩ :=
    T.exists_intervalReference_terminal_of_limitWarp_hits_frontiers
      hp hxOld hxp hvNew hvp
  let qs : T.intervalReference := ⟨q, hq⟩
  let D := T.intervalRealization
  let a := T.intervalReferenceSource qs
  have hqEq : q =
      (Sum.inl (D.toSegmentRealization.segment a) : Gamma.DPath) :=
    T.intervalReference_eq_segment_source qs
  have hqInitialOld : q.initial ∈ C.ladder.frontier alpha := by
    have hinit : q.initial ∈ Gamma.initialSet T.intervalReference := ⟨q, hq, rfl⟩
    rw [T.intervalReference_isLinkageBetween.initialSet_eq] at hinit
    simpa only using hinit.1
  have hqInitialP : q.initial ∈ p.support := hqSupport q.initial_mem_support
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
      (C.ladder.frontier R.later.stage) := by
    obtain ⟨r, hr, hwr⟩ := hwRow
    exact T.interval.ambientInterval_in_outerRoof r hr hwr
  have hwRight : w ∈ (D.rightPrefix a).support :=
    DWeb.KappaLadder.Deferred.limitComponent_support_inter_roof_subset_prefix
      C.legal R.later.stage hp (D.right_mem a).1 hrightExt
        ⟨hwp, hwLaterRoof⟩
  let hstart : Path.initial
      (.inl (D.toSegmentRealization.segment a) : Gamma.DPath) =
        (D.leftPrefix a).finish := by
    exact (D.toSegmentRealization.segment_start a).trans
      (D.left_finish a).symm
  let hinter : (D.leftPrefix a).support ∩
      (D.toSegmentRealization.segment a).support ⊆
        {(D.leftPrefix a).finish} := (D.prefix_inter a).subset
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
    · have hwOldRoof : w ∈ Gamma.roof (C.ladder.frontier alpha) := by
        have hwRaw :=
          DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier
            C.legal alpha
              ⟨Sum.inl (D.leftPrefix a), (D.left_mem a).1, hwLeft⟩
        change w ∈ Gamma.roof (C.ladder.frontier alpha)
        rw [C.ladder.frontier_eq_essential_terminalFrontier
          C.legal.roofsSourceAtStages, Gamma.roof_essential]
        exact hwRaw
      have hwCaptured : w ∈ (C.ladder.frontier alpha) := by
        rw [← T.interval.ambientInterval_vertexSet_inter_oldRoof]
        exact ⟨hwRow, by
          simpa only using hwOldRoof⟩
      have hwOld : w ∈ C.ladder.frontier alpha := by
        simpa only using hwCaptured
      have hwx : w = x :=
        C.limitWarp_frontier_hit_unique hp hwOld hwp hxOld hxp
      rw [hwx, ← hqInitial]
      exact q.initial_mem_support
    · rw [hqEq]
      exact hwSegment
  exact ⟨q, hq, hwQ, hqTerminal, hqSupport⟩

end StagePostClosureIntervalTransaction

#print axioms StagePostClosureIntervalTransaction.intervalGlobalReferenceEmbedding
#print axioms
  StagePostClosureIntervalTransaction.exists_intervalReference_terminal_of_limitWarp_hits_frontiers
namespace StagePostClosureIntervalTransaction

#print axioms exists_intervalReference_containing_of_limitWarp_hits_frontiers

end StagePostClosureIntervalTransaction

end Erdos599.Blueprint.LinkageBlueprint
