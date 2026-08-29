/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingConcreteControls
import ErdosProblems.Erdos599.GroundingWeakChronology
import ErdosProblems.Erdos599.LadderHangingProvenance
import ErdosProblems.Erdos599.LadderLimitHitClosure

/-!
# The hanging-ladder rank in Assertion 8.19

This file constructs the regressive countable collision data used in
Assertion 8.19.  The first step is independent of the popular separator:
the exact successor and limit laws of a legal ladder imply that every
accumulated component starts either at an original source or at a marker
inserted no later than that accumulated stage.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The construction laws in `IsLegal` imply initial-vertex provenance for
every accumulated component, not only for the concrete canonical ladder.
At a successor this follows from exact arrow provenance; at a genuine limit
it follows from the initial-thread description of `GrowingWarpChain.limitPaths`.
-/
theorem IsLegal.hasAccumulatedInitialProvenance
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal) :
    L.HasAccumulatedInitialProvenance := by
  have hprovenance : ∀ (o : Ordinal.{u}) (ho : o ≤ kappa.ord)
      (p : Gamma.DPath), p ∈ L.accumulated ⟨o, ho⟩ →
        p.initial ∈ Gamma.source ∨
          ∃ b : Ladder.Stage kappa,
            Ladder.Stage.succExtended b ≤ ⟨o, ho⟩ ∧
              L.marker b = some p.initial := by
    intro o
    induction o using Ordinal.limitRecOn with
    | zero =>
        intro ho p hp
        have hzero : (⟨0, ho⟩ : Ladder.ExtendedStage kappa) =
            Ladder.zeroStage kappa := Subtype.ext rfl
        have hpTrivial : p ∈ Gamma.trivialWave := by
          rw [hzero, hlegal.initialStage] at hp
          exact hp
        exact Or.inl (Gamma.initialSet_trivialWave ▸ ⟨p, hpTrivial, rfl⟩)
    | add_one o ih =>
        intro ho p hp
        have hoStage : o < kappa.ord := (Order.add_one_le_iff).1 ho
        let a : Ladder.Stage kappa := ⟨o, hoStage⟩
        have hsucc : (⟨o + 1, ho⟩ : Ladder.ExtendedStage kappa) =
            Ladder.Stage.succExtended a := Subtype.ext rfl
        have hpSuccessor : p ∈ L.successorWarp a := by
          change p ∈ L.accumulated (Ladder.Stage.succExtended a)
          rw [← hsucc]
          exact hp
        rcases hlegal.successorComponentProvenance a p hpSuccessor with
            ⟨q, hq, hqp⟩ | ⟨y, hy, rfl⟩
        · have hoo : o ≤ o + 1 := by
            rw [← Order.succ_eq_add_one]
            exact le_succ o
          have hcurrent : Ladder.Stage.toExtended a =
              (⟨o, le_trans hoo ho⟩ : Ladder.ExtendedStage kappa) :=
            Subtype.ext rfl
          have hqAt : q ∈ L.accumulated
              (⟨o, le_trans hoo ho⟩ : Ladder.ExtendedStage kappa) := by
            rw [← hcurrent]
            exact hq
          rcases ih (le_trans hoo ho) q hqAt with
              hqSource | ⟨b, hbStage, hbMarker⟩
          · exact Or.inl (Gamma.extends_initial hqp.extends ▸ hqSource)
          · refine Or.inr ⟨b, hbStage.trans ?_, ?_⟩
            · change o ≤ o + 1
              exact hoo
            · simpa only [Gamma.extends_initial hqp.extends] using hbMarker
        · exact Or.inr ⟨a, le_rfl, by simpa using hy⟩
    | limit o hoLimit ih =>
        intro ho p hp
        let a : Ladder.ExtendedStage kappa := ⟨o, ho⟩
        obtain ⟨C, hstage, hlimit⟩ := hlegal.limitStages a hoLimit
        have hpInitial : p.initial ∈ C.initialUnion := by
          rw [← C.initialSet_limitPaths Gamma, ← hlimit]
          exact ⟨p, hp, rfl⟩
        obtain ⟨b, q, hq, hqp⟩ := Set.mem_iUnion.1 hpInitial
        have hbo : b.1 ≤ kappa.ord := b.2.le.trans ho
        have hqAccumulated : q ∈ L.accumulated ⟨b.1, hbo⟩ := by
          rw [← hstage b]
          exact hq
        rcases ih b.1 b.2 hbo q hqAccumulated with
            hqSource | ⟨c, hcStage, hcMarker⟩
        · exact Or.inl (hqp ▸ hqSource)
        · exact Or.inr ⟨c, hcStage.trans b.2.le, by
            simpa only [hqp] using hcMarker⟩
  intro a p hp
  exact hprovenance a.1 a.2 p hp

/-- Every hanging member of the limiting ladder has a marker as its initial
vertex.  This is the component owner used as the ordinal rank in
Assertion 8.19. -/
theorem IsLegal.exists_markerStage_of_mem_limitWarp_of_hanging
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma p) :
    ∃ b : Ladder.Stage kappa, L.marker b = some p.initial := by
  rcases hlegal.hasAccumulatedInitialProvenance
      (Ladder.finalStage kappa) p hp with hpSource | ⟨b, _hb, hmarker⟩
  · exact False.elim (hhang hpSource)
  · exact ⟨b, hmarker⟩

/-- The uniquely determined owner stage of a hanging limiting component. -/
noncomputable def hangingComponentStage
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (p : Gamma.DPath) (hp : p ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma p) :
    Ladder.Stage kappa :=
  Classical.choose
    (hlegal.exists_markerStage_of_mem_limitWarp_of_hanging hp hhang)

@[simp]
theorem marker_hangingComponentStage
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (p : Gamma.DPath) (hp : p ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma p) :
    L.marker (L.hangingComponentStage hlegal p hp hhang) = some p.initial :=
  Classical.choose_spec
    (hlegal.exists_markerStage_of_mem_limitWarp_of_hanging hp hhang)

/-! ## Index-wise collision owners -/

/-- Source injectivity makes a joined in-fan path uniquely determined by
its initial ordinal index, provided the common apex is not a source. -/
theorem joinedFamily_path_eq_of_same_initialIndex
    {W : Type u} {web : DWeb W} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed web kappa) (hU : U.SourceIndexed)
    {c : W} (F : Popular.JoinedFamily web {c}) (hc : c ∉ web.source)
    {p q : DirectedPath.FinitePath web.graph} (hp : p ∈ F.paths) (hq : q ∈ F.paths)
    (hpqIndex :
      U.f ⟨p.start, F.starts_in_source hp⟩ =
        U.f ⟨q.start, F.starts_in_source hq⟩) :
    p = q := by
  have hsource :
      (⟨p.start, F.starts_in_source hp⟩ : web.source) =
        ⟨q.start, F.starts_in_source hq⟩ := hU hpqIndex
  have hstart : p.start = q.start := congrArg Subtype.val hsource
  by_contra hpq
  have hcommon : p.start ∈ p.support ∩ q.support :=
    ⟨p.start_mem_support, hstart ▸ q.start_mem_support⟩
  have hapex : p.start = c := by
    simpa only [Set.mem_singleton_iff] using F.joined hp hq hpq hcommon
  exact hc (hapex ▸ F.starts_in_source hp)

variable (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)

private abbrev AuxiliaryInput := L.popularAuxiliaryInput hL.legal

private abbrev AuxiliaryIndexed := L.popularAuxiliaryIndexed hL

/-- The exact local chronology statement used in source Assertion 8.19.
It is deliberately path-local: unlike the false unconditional strict
source--target chronology, it assumes an off-apex trace contact with a
hanging limiting component. -/
def HasAssertion819Chronology
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) : Prop :=
  ∀ (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (p : DirectedPath.FinitePath
      (L.popularAuxiliaryInput hL.legal).lambda.graph)
    (hp : p ∈ (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths)
    (Y : Gamma.DPath)
    (hY : Y ∈ (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y)
    (z : PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords)
    (hzY : z ∈ PopularSwitching.ladderTrace
      (L.popularAuxiliaryInput hL.legal) Y)
    (hzp : z ∈ p.support)
    (hzapex : z ≠ PopularGroundingBridge.requestAuxVertex r)
    (v : V) (hvY : v ∈ Y.support)
    (hzexit : (L.popularAuxiliaryInput hL.legal).gadgetExit z = some v),
    L.hangingComponentStage hL.legal Y
        (by simpa only [KappaLadder.popularAuxiliaryInput] using hY) hhang <
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.start,
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r)
            {q | GroundingConcreteControls.hangingLadderCollision
              (L.popularAuxiliaryInput hL.legal) S.cut r q})
            |>.starts_in_source hp⟩

/-- A type-valued owner for an initial index of the exceptional subfan.
Keeping all membership proofs in the record makes the subsequent
`Classical.choose` definition proof-independent. -/
structure Assertion819CollisionOwner
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) where
  path : DirectedPath.FinitePath
    (L.popularAuxiliaryInput hL.legal).lambda.graph
  path_mem : path ∈ (PopularSwitching.restrictPaths
    (PopularGroundingBridge.requestFan S r)
    {q | GroundingConcreteControls.hangingLadderCollision
      (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths
  index_eq : (L.popularAuxiliaryIndexed hL).f
      ⟨path.start,
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.popularAuxiliaryInput hL.legal) S.cut r q})
          |>.starts_in_source path_mem⟩ = a
  component : Gamma.DPath
  component_mem : component ∈ L.limitWarp
  component_hanging : PopularAuxiliary.IsHangingPath Gamma component
  traceContact : PopularAuxiliary.Input.LambdaVertex V
    L.groundedInfiniteRecords
  traceContact_mem_trace : traceContact ∈ PopularSwitching.ladderTrace
    (L.popularAuxiliaryInput hL.legal) component
  traceContact_ne_apex : traceContact ≠
    PopularGroundingBridge.requestAuxVertex r
  traceContact_mem_path : traceContact ∈ path.support
  contact : V
  contact_mem_component : contact ∈ component.support
  traceContact_exit : (L.popularAuxiliaryInput hL.legal).gadgetExit
    traceContact = some contact

/-- Every exceptional initial index has a concrete collision owner. -/
theorem assertion819CollisionOwner_nonempty
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    {a : Stationary.Below kappa}
    (ha : a ∈ Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.popularAuxiliaryInput hL.legal) S.cut r q}).starts_in_source) :
    Nonempty (L.Assertion819CollisionOwner hL S r a) := by
  obtain ⟨p, hp, hpa⟩ := ha
  have hcollision := hp.2
  change GroundingConcreteControls.hangingLadderCollision
    (L.popularAuxiliaryInput hL.legal) S.cut r p at hcollision
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
        simpa only [KappaLadder.popularAuxiliaryInput] using hY
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
        simpa only [KappaLadder.popularAuxiliaryInput] using hY
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
noncomputable def assertion819CollisionOwner?
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) :
    Option (L.Assertion819CollisionOwner hL S r a) := by
  classical
  exact if ha : Nonempty (L.Assertion819CollisionOwner hL S r a) then
    some (Classical.choice ha)
  else none

theorem assertion819CollisionOwner?_eq_some_of_mem
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    {a : Stationary.Below kappa}
    (ha : a ∈ Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.popularAuxiliaryInput hL.legal) S.cut r q}).starts_in_source) :
    ∃ d : L.Assertion819CollisionOwner hL S r a,
      L.assertion819CollisionOwner? hL S r a = some d := by
  let hn := L.assertion819CollisionOwner_nonempty hL S r ha
  rw [assertion819CollisionOwner?, dif_pos hn]
  exact ⟨Classical.choice hn, rfl⟩

/-- The component-owner rank, totalized by the identity away from the
exceptional initial-index set. -/
noncomputable def assertion819Rank
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) : Stationary.Below kappa :=
  match L.assertion819CollisionOwner? hL S r a with
  | none => a
  | some d => L.hangingComponentStage hL.legal d.component
      d.component_mem d.component_hanging

/-- A hanging limiting component whose unique marker-owner is `a`.
Unlike a collision owner, this datum depends only on the stage and not on a
particular request or fan path.  This is essential because the pressing-down
lemma indexes the common countable trace by the regressive rank. -/
structure Assertion819StageComponent
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) where
  component : Gamma.DPath
  component_mem : component ∈ L.limitWarp
  component_hanging : PopularAuxiliary.IsHangingPath Gamma component
  stage_eq : L.hangingComponentStage hL.legal component
      component_mem component_hanging = a

/-- Any collision owner supplies a stage component at its owner rank. -/
def Assertion819CollisionOwner.toStageComponent
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut}
    {a : Stationary.Below kappa}
    (d : L.Assertion819CollisionOwner hL S r a) :
    L.Assertion819StageComponent hL S r
      (L.hangingComponentStage hL.legal d.component
        d.component_mem d.component_hanging) where
  component := d.component
  component_mem := d.component_mem
  component_hanging := d.component_hanging
  stage_eq := rfl

/-- At most one limiting component is owned by a given marker stage. -/
theorem Assertion819StageComponent.component_eq
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut}
    {a : Stationary.Below kappa}
    (d e : L.Assertion819StageComponent hL S r a) :
    d.component = e.component := by
  apply DWeb.IsWarp.eq_of_initial_eq Gamma
    (hL.legal.warpStages (Ladder.finalStage kappa))
    d.component_mem e.component_mem
  have hdmarker := L.marker_hangingComponentStage hL.legal d.component
    d.component_mem d.component_hanging
  have hemarker := L.marker_hangingComponentStage hL.legal e.component
    e.component_mem e.component_hanging
  rw [d.stage_eq] at hdmarker
  rw [e.stage_eq] at hemarker
  exact Option.some.inj (hdmarker.symm.trans hemarker)

/-- Choose the unique stage component when it exists, and `none` otherwise. -/
noncomputable def assertion819StageComponent?
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) :
    Option (L.Assertion819StageComponent hL S r a) := by
  classical
  exact if ha : Nonempty (L.Assertion819StageComponent hL S r a) then
    some (Classical.choice ha)
  else none

theorem assertion819StageComponent?_eq_some_of_nonempty
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa)
    (ha : Nonempty (L.Assertion819StageComponent hL S r a)) :
    ∃ d : L.Assertion819StageComponent hL S r a,
      L.assertion819StageComponent? hL S r a = some d := by
  rw [assertion819StageComponent?, dif_pos ha]
  exact ⟨Classical.choice ha, rfl⟩

/-- The off-apex auxiliary trace of the uniquely owned component at a stage,
and the empty set when no hanging component is owned there. -/
noncomputable def assertion819Trace
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) :
    Set (PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords) :=
  match L.assertion819StageComponent? hL S r a with
  | none => ∅
  | some d => PopularSwitching.ladderTrace
      (L.popularAuxiliaryInput hL.legal) d.component \
        {PopularGroundingBridge.requestAuxVertex r}

/-! ## The concrete Assertion 8.19 control package -/

/-- On a collision index, the totalized rank is the owner component's
marker stage. -/
theorem assertion819Rank_eq_of_owner
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa)
    (d : L.Assertion819CollisionOwner hL S r a)
    (hd : L.assertion819CollisionOwner? hL S r a = some d) :
    L.assertion819Rank hL S r a =
      L.hangingComponentStage hL.legal d.component
        d.component_mem d.component_hanging := by
  simp only [assertion819Rank, hd]

/-- When a stage component exists, the totalized trace is exactly its
off-apex Lambda trace. -/
theorem assertion819Trace_eq_of_stageComponent
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa)
    (d : L.Assertion819StageComponent hL S r a)
    (hd : L.assertion819StageComponent? hL S r a = some d) :
    L.assertion819Trace hL S r a =
      PopularSwitching.ladderTrace
        (L.popularAuxiliaryInput hL.legal) d.component \
          {PopularGroundingBridge.requestAuxVertex r} := by
  simp only [assertion819Trace, hd]

/-- Every totalized Assertion 8.19 trace is countable. -/
theorem assertion819Trace_countable
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) :
    (L.assertion819Trace hL S r a).Countable := by
  generalize howner : L.assertion819StageComponent? hL S r a = owner
  cases owner with
  | none => simp only [assertion819Trace, howner, Set.countable_empty]
  | some d =>
      rw [L.assertion819Trace_eq_of_stageComponent hL S r a d howner]
      exact (PopularSwitching.ladderTrace_countable
        (L.popularAuxiliaryInput hL.legal) d.component).mono Set.diff_subset

/-- Every totalized trace avoids its request apex.  On collision indices
this is part of the literal source hypothesis; off those indices the trace
is empty. -/
theorem assertion819Trace_disjoint_apex
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Stationary.Below kappa) :
    Disjoint (L.assertion819Trace hL S r a)
      {PopularGroundingBridge.requestAuxVertex r} := by
  generalize howner : L.assertion819StageComponent? hL S r a = owner
  cases owner with
  | none =>
      simp only [assertion819Trace, howner]
      exact Set.empty_disjoint _
  | some d =>
      rw [L.assertion819Trace_eq_of_stageComponent hL S r a d howner]
      exact Set.disjoint_sdiff_left

/-- A member of the exceptional fan meets the trace chosen at its own
initial index.  Source-index injectivity and the joined-family property show
that the path stored by the collision owner is the given path. -/
theorem assertion819Collision_meets_trace
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (p : DirectedPath.FinitePath
      (L.popularAuxiliaryInput hL.legal).lambda.graph)
    (hp : p ∈ (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths) :
    ∃ x ∈ L.assertion819Trace hL S r
        (L.assertion819Rank hL S r
          ((L.popularAuxiliaryIndexed hL).f
          ⟨p.start,
            (PopularSwitching.restrictPaths
              (PopularGroundingBridge.requestFan S r)
              {q | GroundingConcreteControls.hangingLadderCollision
                (L.popularAuxiliaryInput hL.legal) S.cut r q}).starts_in_source hp⟩)),
      x ∈ p.support := by
  let a : Stationary.Below kappa :=
    (L.popularAuxiliaryIndexed hL).f
      ⟨p.start,
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.popularAuxiliaryInput hL.legal) S.cut r q}).starts_in_source hp⟩
  have ha : a ∈ Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.popularAuxiliaryInput hL.legal) S.cut r q}).starts_in_source := by
    exact ⟨p, hp, rfl⟩
  obtain ⟨d, hd⟩ :=
    L.assertion819CollisionOwner?_eq_some_of_mem hL S r ha
  let b : Stationary.Below kappa :=
    L.hangingComponentStage hL.legal d.component
      d.component_mem d.component_hanging
  have hbNonempty : Nonempty (L.Assertion819StageComponent hL S r b) :=
    ⟨d.toStageComponent⟩
  obtain ⟨e, he⟩ :=
    L.assertion819StageComponent?_eq_some_of_nonempty hL S r b hbNonempty
  have hed : e.component = d.component :=
    Assertion819StageComponent.component_eq
      (L := L) (hL := hL) e d.toStageComponent
  let F := PopularSwitching.restrictPaths
    (PopularGroundingBridge.requestFan S r)
    {q | GroundingConcreteControls.hangingLadderCollision
      (L.popularAuxiliaryInput hL.legal) S.cut r q}
  have hpd : p = d.path := by
    apply joinedFamily_path_eq_of_same_initialIndex
      (L.popularAuxiliaryIndexed hL)
      (L.popularAuxiliaryIndexed_sourceIndexed hL) F
      (PopularGroundingBridge.requestAuxVertex_not_mem_source r)
      hp d.path_mem
    exact d.index_eq.symm
  refine ⟨d.traceContact, ?_, ?_⟩
  · rw [L.assertion819Rank_eq_of_owner hL S r a d hd,
      L.assertion819Trace_eq_of_stageComponent hL S r b e he, hed]
    exact ⟨d.traceContact_mem_trace,
      fun h ↦ d.traceContact_ne_apex (Set.mem_singleton_iff.mp h)⟩
  · rw [hpd]
    exact d.traceContact_mem_path

/-- Once the one genuine chronology inequality of Assertion 8.19 is
available, all remaining rank, countability, apex-avoidance, and collision
fields assemble without further geometric assumptions. -/
noncomputable def assertion819RankData
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (hchronology : L.HasAssertion819Chronology hL S) :
    GroundingConcreteControls.HangingLadderRankData S where
  rank := L.assertion819Rank hL S
  trace := L.assertion819Trace hL S
  rank_regressive := by
    intro r a ha
    obtain ⟨d, hd⟩ :=
      L.assertion819CollisionOwner?_eq_some_of_mem hL S r ha
    rw [L.assertion819Rank_eq_of_owner hL S r a d hd]
    have hlt := hchronology r d.path d.path_mem d.component
      (by simpa only [KappaLadder.popularAuxiliaryInput]
        using d.component_mem)
      d.component_hanging d.traceContact d.traceContact_mem_trace
      d.traceContact_mem_path d.traceContact_ne_apex d.contact
      d.contact_mem_component d.traceContact_exit
    simpa only [d.index_eq] using hlt
  trace_countable := L.assertion819Trace_countable hL S
  trace_disjoint_apex := L.assertion819Trace_disjoint_apex hL S
  collision_meets_trace := L.assertion819Collision_meets_trace hL S

/-- The exact chronology of Assertion 8.19 and the independently constructed
Assertion 8.20 nonstationarity package assemble into source-faithful concrete
controls.  This is the package consumed by the controlled request recursion
and the simultaneous decoder. -/
noncomputable def concreteControls_of_assertions819_820
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (hchronology : L.HasAssertion819Chronology hL S)
    (hfragment : GroundingConcreteControls.HangingFragmentWarpData S) :
    GroundingConcreteControls.ConcreteControls S :=
  GroundingConcreteControls.ConcreteControls.ofData S
    (L.assertion819RankData hL S hchronology) hfragment

end KappaLadder
end DWeb
end Erdos599
