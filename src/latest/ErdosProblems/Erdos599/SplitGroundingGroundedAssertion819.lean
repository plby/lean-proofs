/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedChronology
import ErdosProblems.Erdos599.GroundingAssertion819
import ErdosProblems.Erdos599.GroundingFragmentAssertion820

/-!
# Successor-correct Assertion 8.19 for the grounded split auxiliary

Only genuinely earlier hanging contacts are removed by pressing down.
Equal-stage contacts remain as matched grounded geometry for the normalized
decoder.  This is the split, grounded analogue of the corrected legacy
Assertion 8.19 and does not use a split-to-legacy coercion.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Ladder Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

variable (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
  (hground : IsStationaryBelow kappa L.phiGround)

/-- Initial indices of all literal hanging-ladder collisions at a request. -/
def splitGroundedAssertion819CollisionIndices
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    Set (Below kappa) :=
  Popular.initialIndicesOf (L.splitGroundedPopularAuxiliaryIndexed hL hground)
    (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {p | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r p}).paths
    (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {p | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r p}).starts_in_source

/-- A genuinely bad grounded collision has a hanging owner strictly earlier
than the route's grounded source stage. -/
structure SplitGroundedAssertion819StrictOwner
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Below kappa) where
  owner : L.SplitGroundedAssertion819CollisionOwner hL hground S r a
  stage_lt : L.splitHangingComponentStage hL.legal owner.component
      owner.component_mem owner.component_hanging < a

def splitGroundedAssertion819StrictCollisionIndices
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    Set (Below kappa) :=
  {a | Nonempty (L.SplitGroundedAssertion819StrictOwner hL hground S r a)}

noncomputable def splitGroundedAssertion819StrictOwner?
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Below kappa) :
    Option (L.SplitGroundedAssertion819StrictOwner hL hground S r a) := by
  classical
  exact if ha : Nonempty
      (L.SplitGroundedAssertion819StrictOwner hL hground S r a) then
    some (Classical.choice ha)
  else none

theorem splitGroundedAssertion819StrictOwner?_eq_some_of_nonempty
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Below kappa)
    (ha : Nonempty
      (L.SplitGroundedAssertion819StrictOwner hL hground S r a)) :
    ∃ d, L.splitGroundedAssertion819StrictOwner? hL hground S r a = some d := by
  rw [splitGroundedAssertion819StrictOwner?, dif_pos ha]
  exact ⟨Classical.choice ha, rfl⟩

noncomputable def splitGroundedAssertion819StrictRank
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Below kappa) : Below kappa :=
  match L.splitGroundedAssertion819StrictOwner? hL hground S r a with
  | none => a
  | some d => L.splitHangingComponentStage hL.legal d.owner.component
      d.owner.component_mem d.owner.component_hanging

theorem splitGroundedAssertion819StrictRank_regressive
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    IsRegressiveOn
      (L.splitGroundedAssertion819StrictCollisionIndices hL hground S r)
      (L.splitGroundedAssertion819StrictRank hL hground S r) := by
  intro a ha
  obtain ⟨d, hd⟩ :=
    L.splitGroundedAssertion819StrictOwner?_eq_some_of_nonempty
      hL hground S r a ha
  simpa only [splitGroundedAssertion819StrictRank, hd] using d.stage_lt

theorem splitGroundedAssertion819StrictCollisionIndices_subset_collisionIndices
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    L.splitGroundedAssertion819StrictCollisionIndices hL hground S r ⊆
      L.splitGroundedAssertion819CollisionIndices hL hground S r := by
  rintro a ⟨d⟩
  exact ⟨d.owner.path, d.owner.path_mem, d.owner.index_eq⟩

theorem splitGroundedAssertion819StrictCollision_meets_trace
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (p : FinitePath
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.graph)
    (hp : p ∈ (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).paths)
    (ha : (L.splitGroundedPopularAuxiliaryIndexed hL hground).f
      ⟨p.start, (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
          |>.starts_in_source hp⟩ ∈
        L.splitGroundedAssertion819StrictCollisionIndices hL hground S r) :
    ∃ x ∈ L.splitGroundedAssertion819Trace hL hground S r
        (L.splitGroundedAssertion819StrictRank hL hground S r
          ((L.splitGroundedPopularAuxiliaryIndexed hL hground).f
            ⟨p.start, (PopularSwitching.restrictPaths
              (PopularGroundingBridge.requestFan S r)
              {q | GroundingConcreteControls.hangingLadderCollision
                (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
                |>.starts_in_source hp⟩)),
      x ∈ p.support := by
  let a := (L.splitGroundedPopularAuxiliaryIndexed hL hground).f
    ⟨p.start, (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
        |>.starts_in_source hp⟩
  obtain ⟨d, hd⟩ :=
    L.splitGroundedAssertion819StrictOwner?_eq_some_of_nonempty
      hL hground S r a ha
  let b := L.splitHangingComponentStage hL.legal d.owner.component
    d.owner.component_mem d.owner.component_hanging
  have hb : Nonempty
      (L.SplitGroundedAssertion819StageComponent hL hground S r b) :=
    ⟨d.owner.toStageComponent⟩
  obtain ⟨e, he⟩ :=
    L.splitGroundedAssertion819StageComponent?_eq_some_of_nonempty
      hL hground S r b hb
  have hed : e.component = d.owner.component :=
    SplitGroundedAssertion819StageComponent.component_eq
      (L := L) (hL := hL) (hground := hground) e d.owner.toStageComponent
  let F := PopularSwitching.restrictPaths
    (PopularGroundingBridge.requestFan S r)
    {q | GroundingConcreteControls.hangingLadderCollision
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}
  have hpd : p = d.owner.path := by
    apply joinedFamily_path_eq_of_same_initialIndex
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)
      (L.splitGroundedPopularAuxiliaryIndexed_sourceIndexed hL hground) F
      (PopularGroundingBridge.requestAuxVertex_not_mem_source r)
      hp d.owner.path_mem
    exact d.owner.index_eq.symm
  refine ⟨d.owner.traceContact, ?_, ?_⟩
  · rw [show L.splitGroundedAssertion819StrictRank hL hground S r a = b by
          simp only [splitGroundedAssertion819StrictRank, hd, b],
        L.splitGroundedAssertion819Trace_eq_of_stageComponent
          hL hground S r b e he, hed]
    exact ⟨d.owner.traceContact_mem_trace,
      fun h ↦ d.owner.traceContact_ne_apex (Set.mem_singleton_iff.mp h)⟩
  · rw [hpd]
    exact d.owner.traceContact_mem_path

theorem splitGroundedAssertion819StrictCollisionIndices_nonstationary
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    ¬ IsStationaryBelow kappa
      (L.splitGroundedAssertion819StrictCollisionIndices hL hground S r) := by
  let F := PopularSwitching.restrictPaths
    (PopularGroundingBridge.requestFan S r)
    {p | GroundingConcreteControls.hangingLadderCollision
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r p}
  apply _root_.Erdos599.PopularSwitching.indexSubset_nonstationary_of_regressive_countable_collisions
      (L.splitGroundedPopularAuxiliaryIndexed hL hground) F
      (L.splitGroundedAssertion819StrictCollisionIndices hL hground S r)
      (L.splitGroundedAssertion819StrictRank hL hground S r)
      (L.splitGroundedAssertion819Trace hL hground S r)
  · exact L.splitGroundedAssertion819StrictCollisionIndices_subset_collisionIndices
      hL hground S r
  · exact L.splitGroundedAssertion819StrictRank_regressive hL hground S r
  · exact L.splitGroundedAssertion819Trace_countable hL hground S r
  · exact L.splitGroundedAssertion819Trace_disjoint_apex hL hground S r
  · exact L.splitGroundedAssertion819StrictCollision_meets_trace
      hL hground S r

/-- The selected bad path family consists exactly of paths possessing a
strict owner witness. -/
def splitGroundedAssertion819StrictCollisionPath
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (p : FinitePath
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.graph) : Prop :=
  ∃ hp : p ∈ (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).paths,
    ∃ a, ∃ d : L.SplitGroundedAssertion819StrictOwner hL hground S r a,
      d.owner.path = p

theorem splitGroundedAssertion819StrictCollisionPath_initialIndices
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    Popular.initialIndicesOf (L.splitGroundedPopularAuxiliaryIndexed hL hground)
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {p | L.splitGroundedAssertion819StrictCollisionPath
          hL hground S r p}).paths
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {p | L.splitGroundedAssertion819StrictCollisionPath
          hL hground S r p}).starts_in_source =
      L.splitGroundedAssertion819StrictCollisionIndices hL hground S r := by
  apply Set.Subset.antisymm
  · rintro a ⟨p, hp, hpa⟩
    obtain ⟨hpFan, hpStrict⟩ := hp
    obtain ⟨hpCollision, b, d, hdp⟩ := hpStrict
    let hpAll : p ∈ (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | L.splitGroundedAssertion819StrictCollisionPath
          hL hground S r q}).paths :=
      ⟨hpFan, ⟨hpCollision, b, d, hdp⟩⟩
    have hs :
        (⟨d.owner.path.start,
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r)
            {q | GroundingConcreteControls.hangingLadderCollision
              (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
            |>.starts_in_source d.owner.path_mem⟩ :
              (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source) =
        ⟨p.start,
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r)
            {q | L.splitGroundedAssertion819StrictCollisionPath
              hL hground S r q})
            |>.starts_in_source hpAll⟩ := by
      apply Subtype.ext
      simpa only [hdp]
    have hba : b = a := d.owner.index_eq.symm.trans
      ((congrArg (L.splitGroundedPopularAuxiliaryIndexed hL hground).f hs).trans hpa)
    exact hba ▸ ⟨d⟩
  · rintro a ⟨d⟩
    let hpFan := d.owner.path_mem.1
    have hpStrict : L.splitGroundedAssertion819StrictCollisionPath
        hL hground S r d.owner.path :=
      ⟨d.owner.path_mem, a, d, rfl⟩
    let hp : d.owner.path ∈ (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {p | L.splitGroundedAssertion819StrictCollisionPath
          hL hground S r p}).paths :=
      ⟨hpFan, hpStrict⟩
    refine ⟨d.owner.path, hp, ?_⟩
    have hs :
        (⟨d.owner.path.start,
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r)
            {p | L.splitGroundedAssertion819StrictCollisionPath
              hL hground S r p})
            |>.starts_in_source hp⟩ :
              (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source) =
        ⟨d.owner.path.start,
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r)
            {q | GroundingConcreteControls.hangingLadderCollision
              (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
            |>.starts_in_source d.owner.path_mem⟩ := Subtype.ext rfl
    exact (congrArg (L.splitGroundedPopularAuxiliaryIndexed hL hground).f hs).trans
      d.owner.index_eq

theorem splitGroundedAssertion819StrictCollisionPath_nonstationary
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf
        (L.splitGroundedPopularAuxiliaryIndexed hL hground)
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {p | L.splitGroundedAssertion819StrictCollisionPath
            hL hground S r p}).paths
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {p | L.splitGroundedAssertion819StrictCollisionPath
            hL hground S r p}).starts_in_source) := by
  rw [L.splitGroundedAssertion819StrictCollisionPath_initialIndices
    hL hground S r]
  exact L.splitGroundedAssertion819StrictCollisionIndices_nonstationary
    hL hground S r

/-- The exact grounded split selector controls: strict 8.19 collisions and
the independent finite-fragment family of Assertion 8.20. -/
noncomputable def splitGroundedAssertion819StrictControls
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (HF : GroundingConcreteControls.HangingFragmentWarpData S) :
    GroundingSelection.Controls S where
  hangingLadder r :=
    {p | L.splitGroundedAssertion819StrictCollisionPath hL hground S r p}
  hangingFragment r :=
    {p | GroundingConcreteControls.hangingFragmentCollision
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r p}
  ladderRank := L.splitGroundedAssertion819StrictRank hL hground S
  ladderTrace := L.splitGroundedAssertion819Trace hL hground S
  ladderRank_regressive := by
    intro r
    rw [L.splitGroundedAssertion819StrictCollisionPath_initialIndices
      hL hground S r]
    exact L.splitGroundedAssertion819StrictRank_regressive hL hground S r
  ladderTrace_countable :=
    L.splitGroundedAssertion819Trace_countable hL hground S
  ladderTrace_disjoint_apex :=
    L.splitGroundedAssertion819Trace_disjoint_apex hL hground S
  hangingLadder_meets := by
    intro r p hp
    have ha : (L.splitGroundedPopularAuxiliaryIndexed hL hground).f
        ⟨p.start, (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | L.splitGroundedAssertion819StrictCollisionPath
            hL hground S r q}).starts_in_source hp⟩ ∈
          L.splitGroundedAssertion819StrictCollisionIndices hL hground S r := by
      rw [← L.splitGroundedAssertion819StrictCollisionPath_initialIndices
        hL hground S r]
      exact ⟨p, hp, rfl⟩
    obtain ⟨hpCollision, _a, _d, _hdp⟩ := hp.2
    have hs :
        (⟨p.start, (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
              |>.starts_in_source hpCollision⟩ :
            (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source) =
        ⟨p.start, (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | L.splitGroundedAssertion819StrictCollisionPath
            hL hground S r q}).starts_in_source hp⟩ := Subtype.ext rfl
    have haCollision : (L.splitGroundedPopularAuxiliaryIndexed hL hground).f
        ⟨p.start, (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
              |>.starts_in_source hpCollision⟩ ∈
          L.splitGroundedAssertion819StrictCollisionIndices hL hground S r := by
      simpa only [hs] using ha
    obtain ⟨x, hx, hxp⟩ :=
      L.splitGroundedAssertion819StrictCollision_meets_trace
        hL hground S r p hpCollision haCollision
    refine ⟨x, ?_, hxp⟩
    simpa only [hs] using hx
  fragmentIndices_nonstationary := HF.initialIndices_nonstationary

/-! ## The normalized equal-stage remainder -/

/-- Every source of the grounded split auxiliary is indexed by an element
of `phiGround`; this is pointwise, not an inference from stationarity. -/
theorem splitGroundedPopularAuxiliary_sourceIndex_mem_phiGround
    (x : (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source) :
    (L.splitGroundedPopularAuxiliaryIndexed hL hground).f x ∈ L.phiGround := by
  let I := L.splitGroundedPopularAuxiliaryInput hL.legal
  rcases x with ⟨x, hx⟩
  cases x with
  | old a =>
      let xa : L.groundedFiniteTerminalSet :=
        ⟨a, (I.mem_lambda_source_old a).1 hx⟩
      change L.finiteTerminalIndex xa ∈ L.phiGround
      exact L.finiteTerminalStage_mem_phiGround_of_split hL.legal xa
  | edge a b =>
      exact False.elim (I.not_mem_lambda_source_edge a b hx)
  | proxy i =>
      change L.groundedInfiniteStage i ∈ L.phiGround
      exact (L.groundedInfiniteStage_spec i).1.1

/-- If an index has a literal hanging contact but no strict owner, all its
contacts have the exact grounded source stage. -/
structure SplitGroundedAssertion819EqualMatch
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (a : Below kappa) where
  owner : L.SplitGroundedAssertion819CollisionOwner hL hground S r a
  every_owner_stage_eq :
    ∀ d : L.SplitGroundedAssertion819CollisionOwner hL hground S r a,
      L.splitHangingComponentStage hL.legal d.component
        d.component_mem d.component_hanging = a
  source_grounded : a ∈ L.phiGround

theorem splitGroundedAssertion819_strict_or_equalMatch
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    {a : Below kappa}
    (ha : a ∈ L.splitGroundedAssertion819CollisionIndices hL hground S r) :
    a ∈ L.splitGroundedAssertion819StrictCollisionIndices hL hground S r ∨
      Nonempty
        (L.SplitGroundedAssertion819EqualMatch hL hground S r a) := by
  by_cases hstrict : Nonempty
      (L.SplitGroundedAssertion819StrictOwner hL hground S r a)
  · exact Or.inl hstrict
  · obtain ⟨d, _hd⟩ :=
      L.splitGroundedAssertion819CollisionOwner?_eq_some_of_mem
        hL hground S r ha
    right
    refine ⟨⟨d, ?_, ?_⟩⟩
    · intro e
      rcases (L.hasSplitGroundedAssertion819WeakChronology
        hL hground S r a e).lt_or_eq with hlt | heq
      · exact False.elim
          (hstrict ⟨{ owner := e, stage_lt := hlt }⟩)
      · exact heq
    · exact d.index_eq ▸
        L.splitGroundedPopularAuxiliary_sourceIndex_mem_phiGround
          hL hground
          ⟨d.path.start,
            (PopularSwitching.restrictPaths
              (PopularGroundingBridge.requestFan S r)
              {q | GroundingConcreteControls.hangingLadderCollision
                (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
              |>.starts_in_source d.path_mem⟩

/-- Decoder-facing form: a literal collision path retained by the strict
selector has only matched equal-stage owners. -/
theorem splitGroundedAssertion819EqualMatch_of_collision_of_not_strict
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground))
    (r : PopularGroundingBridge.Request
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (p : FinitePath
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.graph)
    (hp : p ∈ (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}).paths)
    (hnot : ¬ L.splitGroundedAssertion819StrictCollisionPath
      hL hground S r p) :
    Nonempty (L.SplitGroundedAssertion819EqualMatch hL hground S r
      ((L.splitGroundedPopularAuxiliaryIndexed hL hground).f
        ⟨p.start, (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
            |>.starts_in_source hp⟩)) := by
  let a := (L.splitGroundedPopularAuxiliaryIndexed hL hground).f
    ⟨p.start, (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
        |>.starts_in_source hp⟩
  have ha : a ∈
      L.splitGroundedAssertion819CollisionIndices hL hground S r :=
    ⟨p, hp, rfl⟩
  rcases L.splitGroundedAssertion819_strict_or_equalMatch
      hL hground S r ha with hstrict | hequal
  · obtain ⟨d⟩ := hstrict
    apply False.elim
    apply hnot
    refine ⟨hp, a, d, ?_⟩
    let F := PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q}
    have hpd := joinedFamily_path_eq_of_same_initialIndex
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)
      (L.splitGroundedPopularAuxiliaryIndexed_sourceIndexed hL hground) F
      (PopularGroundingBridge.requestAuxVertex_not_mem_source r)
      hp d.owner.path_mem d.owner.index_eq.symm
    exact hpd.symm
  · exact hequal

end KappaLadder
end DWeb
end Erdos599
