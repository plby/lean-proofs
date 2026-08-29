/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedAuxiliary
import ErdosProblems.Erdos599.SplitGroundingEqualHangingStage
import ErdosProblems.Erdos599.GroundingHangingLadderRank

/-!
# Assertion 8.19 rank data for the grounded split auxiliary

The countable-trace and owner-selection construction is independent of
legacy legality.  This module installs it on the grounded split input and
uses the sound split owner stage.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open DirectedPath Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

variable (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
  (hground : Stationary.IsStationaryBelow kappa L.phiGround)

private abbrev AuxiliaryInput := L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev AuxiliaryIndexed := L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- The exact local chronology statement used in source Assertion 8.19.
It is deliberately path-local: unlike the false unconditional strict
source--target chronology, it assumes an off-apex trace contact with a
hanging limiting component. -/
def HasSplitGroundedAssertion819Chronology
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground)) : Prop :=
  ∀ (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (p : DirectedPath.FinitePath
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.graph)
    (hp : p ∈ (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).paths)
    (Y : Gamma.DPath)
    (hY : Y ∈ (L.splitGroundedPopularAuxiliaryInput hL.legal).ladder.paths)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y)
    (z : PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords)
    (hzY : z ∈ PopularSwitching.ladderTrace
      (L.splitGroundedPopularAuxiliaryInput hL.legal) Y)
    (hzp : z ∈ p.support)
    (hzapex : z ≠ PopularGroundingBridge.requestAuxVertex r)
    (v : V) (hvY : v ∈ Y.support)
    (hzexit : (L.splitGroundedPopularAuxiliaryInput hL.legal).gadgetExit z = some v),
    L.splitHangingComponentStage hL.legal Y
        (by simpa only [splitGroundedPopularAuxiliaryInput, limitWarp] using hY) hhang <
      (L.splitGroundedPopularAuxiliaryIndexed hL hground).f
        ⟨p.start,
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r)
            {q | GroundingConcreteControls.hangingLadderCollision
              (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
            |>.starts_in_source hp⟩

/-- A type-valued owner for an initial index of the exceptional subfan.
Keeping all membership proofs in the record makes the subsequent
`Classical.choose` definition proof-independent. -/
structure SplitGroundedAssertion819CollisionOwner
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) where
  path : DirectedPath.FinitePath
    (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.graph
  path_mem : path ∈ (PopularSwitching.restrictPaths
    (PopularGroundingBridge.requestFan S r)
    {q | GroundingConcreteControls.hangingLadderCollision
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).paths
  index_eq : (L.splitGroundedPopularAuxiliaryIndexed hL hground).f
      ⟨path.start,
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
          |>.starts_in_source path_mem⟩ = a
  component : Gamma.DPath
  component_mem : component ∈ L.limitWarp
  component_hanging : PopularAuxiliary.IsHangingPath Gamma component
  traceContact : PopularAuxiliary.Input.LambdaVertex V
    L.groundedInfiniteRecords
  traceContact_mem_trace : traceContact ∈ PopularSwitching.ladderTrace
    (L.splitGroundedPopularAuxiliaryInput hL.legal) component
  traceContact_ne_apex : traceContact ≠
    PopularGroundingBridge.requestAuxVertex r
  traceContact_mem_path : traceContact ∈ path.support
  contact : V
  contact_mem_component : contact ∈ component.support
  traceContact_exit : (L.splitGroundedPopularAuxiliaryInput hL.legal).gadgetExit
    traceContact = some contact

/-- Every exceptional initial index has a concrete collision owner. -/
theorem splitGroundedAssertion819CollisionOwner_nonempty
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    {a : Stationary.Below kappa}
    (ha : a ∈ Popular.initialIndicesOf (L.splitGroundedPopularAuxiliaryIndexed hL hground)
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).paths
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).starts_in_source) :
    Nonempty (L.SplitGroundedAssertion819CollisionOwner hL hground S r a) := by
  obtain ⟨p, hp, hpa⟩ := ha
  have hcollision := hp.2
  change GroundingConcreteControls.hangingLadderCollision
    (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r p at hcollision
  rw [GroundingConcreteControls.hangingLadderCollision_iff] at hcollision
  obtain ⟨Y, hY, hhang, z, hzTrace, hzp⟩ := hcollision
  have hzne : z ≠ PopularGroundingBridge.requestAuxVertex r := by
    exact fun h ↦ hzTrace.2 (Set.mem_singleton_iff.mpr h)
  rcases hzTrace.1 with ⟨v, hvY, rfl⟩ | ⟨e, heY, rfl⟩
  · exact ⟨{
      path := p
      path_mem := hp
      index_eq := hpa
      component := Y
      component_mem := by
        simpa only [splitGroundedPopularAuxiliaryInput, limitWarp] using hY
      component_hanging := hhang
      traceContact := .old v
      traceContact_mem_trace := Or.inl ⟨v, hvY, rfl⟩
      traceContact_ne_apex := hzne
      traceContact_mem_path := hzp
      contact := v
      contact_mem_component := hvY
      traceContact_exit := rfl }⟩
  · rcases e with ⟨u, v⟩
    exact ⟨{
      path := p
      path_mem := hp
      index_eq := hpa
      component := Y
      component_mem := by
        simpa only [splitGroundedPopularAuxiliaryInput, limitWarp] using hY
      component_hanging := hhang
      traceContact := .edge u v
      traceContact_mem_trace := Or.inr ⟨(u, v), heY, rfl⟩
      traceContact_ne_apex := hzne
      traceContact_mem_path := hzp
      contact := u
      contact_mem_component := (Y.edgeSet_subset_support_prod heY).1
      traceContact_exit := rfl }⟩

/-- Choose collision-owner data exactly on the exceptional initial indices.
The option is `none` elsewhere, avoiding any inhabitedness assumption on
the ambient graph or its path type. -/
noncomputable def splitGroundedAssertion819CollisionOwner?
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) :
    Option (L.SplitGroundedAssertion819CollisionOwner hL hground S r a) := by
  classical
  exact if ha : Nonempty (L.SplitGroundedAssertion819CollisionOwner hL hground S r a) then
    some (Classical.choice ha)
  else none

theorem splitGroundedAssertion819CollisionOwner?_eq_some_of_mem
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    {a : Stationary.Below kappa}
    (ha : a ∈ Popular.initialIndicesOf (L.splitGroundedPopularAuxiliaryIndexed hL hground)
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).paths
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).starts_in_source) :
    ∃ d : L.SplitGroundedAssertion819CollisionOwner hL hground S r a,
      L.splitGroundedAssertion819CollisionOwner? hL hground S r a = some d := by
  let hn := L.splitGroundedAssertion819CollisionOwner_nonempty hL hground S r ha
  rw [splitGroundedAssertion819CollisionOwner?, dif_pos hn]
  exact ⟨Classical.choice hn, rfl⟩

/-- The component-owner rank, totalized by the identity away from the
exceptional initial-index set. -/
noncomputable def splitGroundedAssertion819Rank
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) : Stationary.Below kappa :=
  match L.splitGroundedAssertion819CollisionOwner? hL hground S r a with
  | none => a
  | some d => L.splitHangingComponentStage hL.legal d.component
      d.component_mem d.component_hanging

/-- A hanging limiting component whose unique marker-owner is `a`.
Unlike a collision owner, this datum depends only on the stage and not on a
particular request or fan path.  This is essential because the pressing-down
lemma indexes the common countable trace by the regressive rank. -/
structure SplitGroundedAssertion819StageComponent
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) where
  component : Gamma.DPath
  component_mem : component ∈ L.limitWarp
  component_hanging : PopularAuxiliary.IsHangingPath Gamma component
  stage_eq : L.splitHangingComponentStage hL.legal component
      component_mem component_hanging = a

/-- Any collision owner supplies a stage component at its owner rank. -/
def SplitGroundedAssertion819CollisionOwner.toStageComponent
    {S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
    {r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut}
    {a : Stationary.Below kappa}
    (d : L.SplitGroundedAssertion819CollisionOwner hL hground S r a) :
    L.SplitGroundedAssertion819StageComponent hL hground S r
      (L.splitHangingComponentStage hL.legal d.component
        d.component_mem d.component_hanging) where
  component := d.component
  component_mem := d.component_mem
  component_hanging := d.component_hanging
  stage_eq := rfl

/-- At most one limiting component is owned by a given marker stage. -/
theorem SplitGroundedAssertion819StageComponent.component_eq
    {S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
    {r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut}
    {a : Stationary.Below kappa}
    (d e : L.SplitGroundedAssertion819StageComponent hL hground S r a) :
    d.component = e.component := by
  apply DWeb.IsWarp.eq_of_initial_eq Gamma
    (hL.legal.warpStages (Ladder.finalStage kappa))
    d.component_mem e.component_mem
  have hdmarker := L.marker_splitHangingComponentStage hL.legal d.component
    d.component_mem d.component_hanging
  have hemarker := L.marker_splitHangingComponentStage hL.legal e.component
    e.component_mem e.component_hanging
  rw [d.stage_eq] at hdmarker
  rw [e.stage_eq] at hemarker
  exact Option.some.inj (hdmarker.symm.trans hemarker)

/-- Choose the unique stage component when it exists, and `none` otherwise. -/
noncomputable def splitGroundedAssertion819StageComponent?
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) :
    Option (L.SplitGroundedAssertion819StageComponent hL hground S r a) := by
  classical
  exact if ha : Nonempty (L.SplitGroundedAssertion819StageComponent hL hground S r a) then
    some (Classical.choice ha)
  else none

theorem splitGroundedAssertion819StageComponent?_eq_some_of_nonempty
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa)
    (ha : Nonempty (L.SplitGroundedAssertion819StageComponent hL hground S r a)) :
    ∃ d : L.SplitGroundedAssertion819StageComponent hL hground S r a,
      L.splitGroundedAssertion819StageComponent? hL hground S r a = some d := by
  rw [splitGroundedAssertion819StageComponent?, dif_pos ha]
  exact ⟨Classical.choice ha, rfl⟩

/-- The off-apex auxiliary trace of the uniquely owned component at a stage,
and the empty set when no hanging component is owned there. -/
noncomputable def splitGroundedAssertion819Trace
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) :
    Set (PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords) :=
  match L.splitGroundedAssertion819StageComponent? hL hground S r a with
  | none => ∅
  | some d => PopularSwitching.ladderTrace
      (L.splitGroundedPopularAuxiliaryInput hL.legal) d.component \
        {PopularGroundingBridge.requestAuxVertex r}

/-! ## The concrete Assertion 8.19 control package -/

/-- On a collision index, the totalized rank is the owner component's
marker stage. -/
theorem splitGroundedAssertion819Rank_eq_of_owner
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa)
    (d : L.SplitGroundedAssertion819CollisionOwner hL hground S r a)
    (hd : L.splitGroundedAssertion819CollisionOwner? hL hground S r a = some d) :
    L.splitGroundedAssertion819Rank hL hground S r a =
      L.splitHangingComponentStage hL.legal d.component
        d.component_mem d.component_hanging := by
  simp only [splitGroundedAssertion819Rank, hd]

/-- When a stage component exists, the totalized trace is exactly its
off-apex Lambda trace. -/
theorem splitGroundedAssertion819Trace_eq_of_stageComponent
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa)
    (d : L.SplitGroundedAssertion819StageComponent hL hground S r a)
    (hd : L.splitGroundedAssertion819StageComponent? hL hground S r a = some d) :
    L.splitGroundedAssertion819Trace hL hground S r a =
      PopularSwitching.ladderTrace
        (L.splitGroundedPopularAuxiliaryInput hL.legal) d.component \
          {PopularGroundingBridge.requestAuxVertex r} := by
  simp only [splitGroundedAssertion819Trace, hd]

/-- Every totalized Assertion 8.19 trace is countable. -/
theorem splitGroundedAssertion819Trace_countable
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) :
    (L.splitGroundedAssertion819Trace hL hground S r a).Countable := by
  generalize howner : L.splitGroundedAssertion819StageComponent? hL hground S r a = owner
  cases owner with
  | none => simp only [splitGroundedAssertion819Trace, howner, Set.countable_empty]
  | some d =>
      rw [L.splitGroundedAssertion819Trace_eq_of_stageComponent hL hground S r a d howner]
      exact (PopularSwitching.ladderTrace_countable
        (L.splitGroundedPopularAuxiliaryInput hL.legal) d.component).mono Set.diff_subset

/-- Every totalized trace avoids its request apex.  On collision indices
this is part of the literal source hypothesis; off those indices the trace
is empty. -/
theorem splitGroundedAssertion819Trace_disjoint_apex
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) :
    Disjoint (L.splitGroundedAssertion819Trace hL hground S r a)
      {PopularGroundingBridge.requestAuxVertex r} := by
  generalize howner : L.splitGroundedAssertion819StageComponent? hL hground S r a = owner
  cases owner with
  | none =>
      simp only [splitGroundedAssertion819Trace, howner]
      exact Set.empty_disjoint _
  | some d =>
      rw [L.splitGroundedAssertion819Trace_eq_of_stageComponent hL hground S r a d howner]
      exact Set.disjoint_sdiff_left

/-- A member of the exceptional fan meets the trace chosen at its own
initial index.  Source-index injectivity and the joined-family property show
that the path stored by the collision owner is the given path. -/
theorem splitGroundedAssertion819Collision_meets_trace
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (p : DirectedPath.FinitePath
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.graph)
    (hp : p ∈ (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).paths) :
    ∃ x ∈ L.splitGroundedAssertion819Trace hL hground S r
        (L.splitGroundedAssertion819Rank hL hground S r
          ((L.splitGroundedPopularAuxiliaryIndexed hL hground).f
          ⟨p.start,
            (PopularSwitching.restrictPaths
              (PopularGroundingBridge.requestFan S r)
              {q | GroundingConcreteControls.hangingLadderCollision
                (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).starts_in_source hp⟩)),
      x ∈ p.support := by
  let a : Stationary.Below kappa :=
    (L.splitGroundedPopularAuxiliaryIndexed hL hground).f
      ⟨p.start,
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).starts_in_source hp⟩
  have ha : a ∈ Popular.initialIndicesOf (L.splitGroundedPopularAuxiliaryIndexed hL hground)
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).paths
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).starts_in_source := by
    exact ⟨p, hp, rfl⟩
  obtain ⟨d, hd⟩ :=
    L.splitGroundedAssertion819CollisionOwner?_eq_some_of_mem hL hground S r ha
  let b : Stationary.Below kappa :=
    L.splitHangingComponentStage hL.legal d.component
      d.component_mem d.component_hanging
  have hbNonempty : Nonempty (L.SplitGroundedAssertion819StageComponent hL hground S r b) :=
    ⟨d.toStageComponent⟩
  obtain ⟨e, he⟩ :=
    L.splitGroundedAssertion819StageComponent?_eq_some_of_nonempty hL hground S r b hbNonempty
  have hed : e.component = d.component :=
    SplitGroundedAssertion819StageComponent.component_eq
      (L := L) (hL := hL) (hground := hground) e d.toStageComponent
  let F := PopularSwitching.restrictPaths
    (PopularGroundingBridge.requestFan S r)
    {q | GroundingConcreteControls.hangingLadderCollision
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}
  have hpd : p = d.path := by
    apply joinedFamily_path_eq_of_same_initialIndex
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)
      (L.splitGroundedPopularAuxiliaryIndexed_sourceIndexed hL hground) F
      (PopularGroundingBridge.requestAuxVertex_not_mem_source r)
      hp d.path_mem
    exact d.index_eq.symm
  refine ⟨d.traceContact, ?_, ?_⟩
  · rw [L.splitGroundedAssertion819Rank_eq_of_owner hL hground S r a d hd,
      L.splitGroundedAssertion819Trace_eq_of_stageComponent hL hground S r b e he, hed]
    exact ⟨d.traceContact_mem_trace,
      fun h ↦ d.traceContact_ne_apex (Set.mem_singleton_iff.mp h)⟩
  · rw [hpd]
    exact d.traceContact_mem_path

/-- Once the one genuine chronology inequality of Assertion 8.19 is
available, all remaining rank, countability, apex-avoidance, and collision
fields assemble without further geometric assumptions. -/
noncomputable def splitGroundedAssertion819RankData
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (hchronology : L.HasSplitGroundedAssertion819Chronology hL hground S) :
    GroundingConcreteControls.HangingLadderRankData S where
  rank := L.splitGroundedAssertion819Rank hL hground S
  trace := L.splitGroundedAssertion819Trace hL hground S
  rank_regressive := by
    intro r a ha
    obtain ⟨d, hd⟩ :=
      L.splitGroundedAssertion819CollisionOwner?_eq_some_of_mem hL hground S r ha
    rw [L.splitGroundedAssertion819Rank_eq_of_owner hL hground S r a d hd]
    have hlt := hchronology r d.path d.path_mem d.component
      (by simpa only [splitGroundedPopularAuxiliaryInput, limitWarp]
        using d.component_mem)
      d.component_hanging d.traceContact d.traceContact_mem_trace
      d.traceContact_mem_path d.traceContact_ne_apex d.contact
      d.contact_mem_component d.traceContact_exit
    simpa only [d.index_eq] using hlt
  trace_countable := L.splitGroundedAssertion819Trace_countable hL hground S
  trace_disjoint_apex := L.splitGroundedAssertion819Trace_disjoint_apex hL hground S
  collision_meets_trace := L.splitGroundedAssertion819Collision_meets_trace hL hground S

/-- The exact chronology of Assertion 8.19 and the independently constructed
Assertion 8.20 nonstationarity package assemble into source-faithful concrete
controls.  This is the package consumed by the controlled request recursion
and the simultaneous decoder. -/
noncomputable def splitGroundedConcreteControls_of_assertions819_820
    (S : Popular.PopularSeparator (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (hchronology : L.HasSplitGroundedAssertion819Chronology hL hground S)
    (hfragment : GroundingConcreteControls.HangingFragmentWarpData S) :
    GroundingConcreteControls.ConcreteControls S :=
  GroundingConcreteControls.ConcreteControls.ofData S
    (L.splitGroundedAssertion819RankData hL hground S hchronology) hfragment

end KappaLadder
end DWeb
end Erdos599
