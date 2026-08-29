/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingHangingCollisionSplit
import ErdosProblems.Erdos599.GroundingTargetPureChronology

/-!
# The successor-corrected form of Assertion 8.19

For the literal successor-normalized ladder, the owner of a hanging
component met by a local fan path is only weakly below the source index.
The equality case is real: a route may meet a component born at its own
source stage.  Consequently the printed pressing-down argument applies to
the strict part only.

This file records that correction without replacing weak chronology by a
false strict statement.  The strict part is nonstationary by the original
countable-trace argument.  After the fan is restricted to `phiGround`, the
equal part is the component paired with the path's own grounded source
stage, so it is matched source geometry rather than a bad collision.  The
file exports that exact equality certificate for the decoder.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

namespace PopularSwitching

open DirectedPath Stationary

universe u

variable {V : Type u}

/-- Localized form of the countable-collision pressing-down argument.
Only the indicated subset of the initial indices has to be regressive. -/
theorem indexSubset_nonstationary_of_regressive_countable_collisions
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed Gamma kappa) {S : Set V}
    (F : Popular.JoinedFamily Gamma S)
    (A : Set (Stationary.Below kappa))
    (rank : Stationary.Below kappa → Stationary.Below kappa)
    (collision : Stationary.Below kappa → Set V)
    (hA : A ⊆ Popular.initialIndicesOf U F.paths F.starts_in_source)
    (hrank : IsRegressiveOn A rank)
    (hcountable : ∀ i, (collision i).Countable)
    (hdisjoint : ∀ i, Disjoint (collision i) S)
    (hmeet : ∀ p (hp : p ∈ F.paths),
      U.f ⟨p.start, F.starts_in_source hp⟩ ∈ A →
      ∃ x ∈ collision (rank (U.f ⟨p.start, F.starts_in_source hp⟩)),
        x ∈ p.support) :
    ¬ IsStationaryBelow kappa A := by
  intro hstationary
  obtain ⟨i, hi⟩ :=
    pressingDown U.uncountable U.regular hstationary hrank
  let P : Set (FinitePath Gamma.graph) :=
    {p | ∃ hp : p ∈ F.paths,
      U.f ⟨p.start, F.starts_in_source hp⟩ ∈ A ∧
        rank (U.f ⟨p.start, F.starts_in_source hp⟩) = i}
  let Fi : Popular.JoinedFamily Gamma S := restrictPaths F P
  have hmeet_i : ∀ p ∈ Fi.paths, ∃ x ∈ collision i, x ∈ p.support := by
    intro p hp
    obtain ⟨hpF, hpP⟩ := hp
    obtain ⟨hpF', _hpA, hrankp⟩ := hpP
    obtain ⟨x, hxc, hxp⟩ := hmeet p hpF _hpA
    have hsource :
        (⟨p.start, F.starts_in_source hpF⟩ : Gamma.source) =
          ⟨p.start, F.starts_in_source hpF'⟩ := Subtype.ext rfl
    refine ⟨x, ?_, hxp⟩
    simpa only [hsource, hrankp] using hxc
  have hnonstationary :
      ¬ IsStationaryBelow kappa
        (Popular.initialIndicesOf U Fi.paths Fi.starts_in_source) :=
    PopularAuxiliary.Input.joinedFamily_initialIndices_nonstationary_of_meets_countable
      U Fi (hcountable i) (hdisjoint i) hmeet_i
  apply hnonstationary
  apply hi.mono
  rintro a ⟨ha, hra⟩
  obtain ⟨p, hp, hpa⟩ := hA ha
  have hpP : p ∈ P := by
    refine ⟨hp, ?_, ?_⟩
    · exact hpa ▸ ha
    · exact (congrArg rank hpa).trans hra
  refine ⟨p, ⟨hp, hpP⟩, ?_⟩
  have hsource :
      (⟨p.start, Fi.starts_in_source ⟨hp, hpP⟩⟩ : Gamma.source) =
        ⟨p.start, F.starts_in_source hp⟩ := Subtype.ext rfl
  exact (congrArg U.f hsource).trans hpa

end PopularSwitching

namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Ladder Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

variable (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)

/-- The complete initial-index set of the literal hanging-ladder collision
subfamily at one request. -/
def assertion819CollisionIndices
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    Set (Below kappa) :=
  Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
    (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {p | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r p}).paths
    (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {p | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r p}).starts_in_source

/-- The exact weak chronology required after successor normalization.
It quantifies over the collision owner actually used by the rank and says
only that its birth stage is at most the source index. -/
def HasAssertion819WeakChronology
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) : Prop :=
  ∀ (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Below kappa) (d : L.Assertion819CollisionOwner hL S r a),
    L.hangingComponentStage hL.legal d.component
      d.component_mem d.component_hanging ≤ a

/-- Pointwise successor-roof transport implies the exact weak collision
chronology.  This is the bridge from the graph-theoretic transport lemmas:
once a contact lies in the successor roof of its source stage, the hanging
component owner cannot be later than that source stage. -/
theorem hasAssertion819WeakChronology_of_contact_successorRoof
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (hroof : ∀
      (r : PopularGroundingBridge.Request
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (a : Below kappa) (d : L.Assertion819CollisionOwner hL S r a),
      d.contact ∈ Gamma.roof
        (L.frontier (L.successorStage hL.legal a))) :
    L.HasAssertion819WeakChronology hL S := by
  intro r a d
  exact hL.legal.hangingComponentStage_le_of_support_mem_roof_successor
    a d.component_mem d.component_hanging d.contact_mem_component
      (hroof r a d)

/-- Target-pure successor-roof transport supplies the weak chronology for
every literal collision owner.  This is the unconditional successor-correct
replacement for the false global strict chronology. -/
theorem hasAssertion819WeakChronology
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :
    L.HasAssertion819WeakChronology hL S :=
  L.hasAssertion819WeakChronology_of_contact_successorRoof hL S
    (fun r a d ↦
      L.assertion819CollisionOwner_contact_mem_successorRoof hL S r a d)

/-- An owner witnessing a genuinely bad collision is strictly earlier than
the path's source stage.  The strict witness, rather than an arbitrary
collision owner, is what the pressing-down choice must select. -/
structure Assertion819StrictOwner
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Below kappa) where
  owner : L.Assertion819CollisionOwner hL S r a
  stage_lt : L.hangingComponentStage hL.legal owner.component
      owner.component_mem owner.component_hanging < a

/-- The indices at which at least one collision owner is genuinely earlier.
Thus a path meeting both its matched component and an earlier component is
always classified as bad. -/
def assertion819StrictCollisionIndices
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    Set (Below kappa) :=
  {a | Nonempty (L.Assertion819StrictOwner hL S r a)}

/-- Choose specifically from strict owners; this avoids the false behavior
of totalizing an arbitrary collision-owner choice. -/
noncomputable def assertion819StrictOwner?
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Below kappa) : Option (L.Assertion819StrictOwner hL S r a) := by
  classical
  exact if ha : Nonempty (L.Assertion819StrictOwner hL S r a) then
    some (Classical.choice ha)
  else none

theorem assertion819StrictOwner?_eq_some_of_nonempty
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Below kappa)
    (ha : Nonempty (L.Assertion819StrictOwner hL S r a)) :
    ∃ d, L.assertion819StrictOwner? hL S r a = some d := by
  rw [assertion819StrictOwner?, dif_pos ha]
  exact ⟨Classical.choice ha, rfl⟩

/-- The regressive rank obtained from the specifically chosen strict owner. -/
noncomputable def assertion819StrictRank
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Below kappa) : Below kappa :=
  match L.assertion819StrictOwner? hL S r a with
  | none => a
  | some d => L.hangingComponentStage hL.legal d.owner.component
      d.owner.component_mem d.owner.component_hanging

/-- The strict-owner rank is regressive exactly on the bad indices. -/
theorem assertion819StrictRank_regressive
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    IsRegressiveOn (L.assertion819StrictCollisionIndices hL S r)
      (L.assertion819StrictRank hL S r) := by
  intro a ha
  obtain ⟨d, hd⟩ :=
    L.assertion819StrictOwner?_eq_some_of_nonempty hL S r a ha
  simpa only [assertion819StrictRank, hd] using d.stage_lt

/-- Every strict collision index is still an index of the literal collision
subfan. -/
theorem assertion819StrictCollisionIndices_subset_collisionIndices
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    L.assertion819StrictCollisionIndices hL S r ⊆
      L.assertion819CollisionIndices hL S r := by
  rintro a ⟨d⟩
  exact ⟨d.owner.path, d.owner.path_mem, d.owner.index_eq⟩

/-- A collision path at a strict index meets the trace chosen from a strict
owner at that index.  The joined-family uniqueness lemma identifies the two
paths even when the path has several component contacts. -/
theorem assertion819StrictCollision_meets_trace
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph)
    (hp : p ∈ (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths)
    (ha : (L.popularAuxiliaryIndexed hL).f
      ⟨p.start, (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.popularAuxiliaryInput hL.legal) S.cut r q})
          |>.starts_in_source hp⟩ ∈
        L.assertion819StrictCollisionIndices hL S r) :
    ∃ x ∈ L.assertion819Trace hL S r
        (L.assertion819StrictRank hL S r
          ((L.popularAuxiliaryIndexed hL).f
            ⟨p.start, (PopularSwitching.restrictPaths
              (PopularGroundingBridge.requestFan S r)
              {q | GroundingConcreteControls.hangingLadderCollision
                (L.popularAuxiliaryInput hL.legal) S.cut r q})
                |>.starts_in_source hp⟩)),
      x ∈ p.support := by
  let a := (L.popularAuxiliaryIndexed hL).f
    ⟨p.start, (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r q})
        |>.starts_in_source hp⟩
  obtain ⟨d, hd⟩ :=
    L.assertion819StrictOwner?_eq_some_of_nonempty hL S r a ha
  let b := L.hangingComponentStage hL.legal d.owner.component
    d.owner.component_mem d.owner.component_hanging
  have hb : Nonempty (L.Assertion819StageComponent hL S r b) :=
    ⟨d.owner.toStageComponent⟩
  obtain ⟨e, he⟩ :=
    L.assertion819StageComponent?_eq_some_of_nonempty hL S r b hb
  have hed : e.component = d.owner.component :=
    Assertion819StageComponent.component_eq
      (L := L) (hL := hL) e d.owner.toStageComponent
  let F := PopularSwitching.restrictPaths
    (PopularGroundingBridge.requestFan S r)
    {q | GroundingConcreteControls.hangingLadderCollision
      (L.popularAuxiliaryInput hL.legal) S.cut r q}
  have hpd : p = d.owner.path := by
    apply joinedFamily_path_eq_of_same_initialIndex
      (L.popularAuxiliaryIndexed hL)
      (L.popularAuxiliaryIndexed_sourceIndexed hL) F
      (PopularGroundingBridge.requestAuxVertex_not_mem_source r)
      hp d.owner.path_mem
    exact d.owner.index_eq.symm
  refine ⟨d.owner.traceContact, ?_, ?_⟩
  · rw [show L.assertion819StrictRank hL S r a = b by
          simp only [assertion819StrictRank, hd, b],
        L.assertion819Trace_eq_of_stageComponent hL S r b e he, hed]
    exact ⟨d.owner.traceContact_mem_trace,
      fun h ↦ d.owner.traceContact_ne_apex
        (Set.mem_singleton_iff.mp h)⟩
  · rw [hpd]
    exact d.owner.traceContact_mem_path

/-- Corrected Assertion 8.19: the indices with any genuinely earlier
hanging contact are nonstationary. -/
theorem assertion819StrictCollisionIndices_nonstationary
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    ¬ IsStationaryBelow kappa
      (L.assertion819StrictCollisionIndices hL S r) := by
  let F := PopularSwitching.restrictPaths
    (PopularGroundingBridge.requestFan S r)
    {p | GroundingConcreteControls.hangingLadderCollision
      (L.popularAuxiliaryInput hL.legal) S.cut r p}
  apply _root_.Erdos599.PopularSwitching.indexSubset_nonstationary_of_regressive_countable_collisions
      (L.popularAuxiliaryIndexed hL) F
      (L.assertion819StrictCollisionIndices hL S r)
      (L.assertion819StrictRank hL S r)
      (L.assertion819Trace hL S r)
  · exact L.assertion819StrictCollisionIndices_subset_collisionIndices hL S r
  · exact L.assertion819StrictRank_regressive hL S r
  · exact L.assertion819Trace_countable hL S r
  · exact L.assertion819Trace_disjoint_apex hL S r
  · exact L.assertion819StrictCollision_meets_trace hL S r

/-- The exact bad path family: the path has a strict owner witness. -/
def assertion819StrictCollisionPath
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph) : Prop :=
  ∃ hp : p ∈ (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths,
    ∃ a, ∃ d : L.Assertion819StrictOwner hL S r a,
      d.owner.path = p

/-- Initial indices of the exact bad path family are precisely the indices
with a strict owner. -/
theorem assertion819StrictCollisionPath_initialIndices
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {p | L.assertion819StrictCollisionPath hL S r p}).paths
      (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {p | L.assertion819StrictCollisionPath hL S r p}).starts_in_source =
      L.assertion819StrictCollisionIndices hL S r := by
  apply Set.Subset.antisymm
  · rintro a ⟨p, hp, hpa⟩
    obtain ⟨_hpFan, hpStrict⟩ := hp
    obtain ⟨hpCollision, b, d, hdp⟩ := hpStrict
    let hpAll : p ∈ (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | L.assertion819StrictCollisionPath hL S r q}).paths :=
      ⟨_hpFan, ⟨hpCollision, b, d, hdp⟩⟩
    have hs :
        (⟨d.owner.path.start,
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r)
            {q | GroundingConcreteControls.hangingLadderCollision
              (L.popularAuxiliaryInput hL.legal) S.cut r q})
            |>.starts_in_source d.owner.path_mem⟩ :
              (L.popularAuxiliaryInput hL.legal).lambda.source) =
        ⟨p.start,
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r)
            {q | L.assertion819StrictCollisionPath hL S r q})
            |>.starts_in_source hpAll⟩ := by
      apply Subtype.ext
      simpa only [hdp]
    have hba : b = a := d.owner.index_eq.symm.trans
      ((congrArg (L.popularAuxiliaryIndexed hL).f hs).trans hpa)
    exact hba ▸ ⟨d⟩
  · rintro a ⟨d⟩
    let hpFan := d.owner.path_mem.1
    have hpStrict : L.assertion819StrictCollisionPath hL S r d.owner.path :=
      ⟨d.owner.path_mem, a, d, rfl⟩
    let hp : d.owner.path ∈ (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {p | L.assertion819StrictCollisionPath hL S r p}).paths :=
      ⟨hpFan, hpStrict⟩
    refine ⟨d.owner.path, hp, ?_⟩
    have hs :
        (⟨d.owner.path.start,
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r)
            {p | L.assertion819StrictCollisionPath hL S r p})
            |>.starts_in_source hp⟩ :
              (L.popularAuxiliaryInput hL.legal).lambda.source) =
        ⟨d.owner.path.start,
          (PopularSwitching.restrictPaths
            (PopularGroundingBridge.requestFan S r)
            {q | GroundingConcreteControls.hangingLadderCollision
              (L.popularAuxiliaryInput hL.legal) S.cut r q})
            |>.starts_in_source d.owner.path_mem⟩ := Subtype.ext rfl
    exact (congrArg (L.popularAuxiliaryIndexed hL).f hs).trans
      d.owner.index_eq

theorem assertion819StrictCollisionPath_nonstationary
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {p | L.assertion819StrictCollisionPath hL S r p}).paths
        (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {p | L.assertion819StrictCollisionPath hL S r p}).starts_in_source) := by
  rw [L.assertion819StrictCollisionPath_initialIndices hL S r]
  exact L.assertion819StrictCollisionIndices_nonstationary hL S r

/-- Existing generic selection machinery can be driven directly by the
strict 8.19 family and the exact 8.20 fragment theorem.  In particular this
constructor does not pass through `ConcreteControls`, whose demand that the
entire hanging-collision family be regressive is false after successor
normalization. -/
noncomputable def assertion819StrictControls
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (HF : GroundingConcreteControls.HangingFragmentWarpData S) :
    GroundingSelection.Controls S where
  hangingLadder r := {p | L.assertion819StrictCollisionPath hL S r p}
  hangingFragment r :=
    {p | GroundingConcreteControls.hangingFragmentCollision
      (L.popularAuxiliaryInput hL.legal) S.cut r p}
  ladderRank := L.assertion819StrictRank hL S
  ladderTrace := L.assertion819Trace hL S
  ladderRank_regressive := by
    intro r
    rw [L.assertion819StrictCollisionPath_initialIndices hL S r]
    exact L.assertion819StrictRank_regressive hL S r
  ladderTrace_countable := L.assertion819Trace_countable hL S
  ladderTrace_disjoint_apex := L.assertion819Trace_disjoint_apex hL S
  hangingLadder_meets := by
    intro r p hp
    have ha : (L.popularAuxiliaryIndexed hL).f
        ⟨p.start, (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | L.assertion819StrictCollisionPath hL S r q})
            |>.starts_in_source hp⟩ ∈
          L.assertion819StrictCollisionIndices hL S r := by
      rw [← L.assertion819StrictCollisionPath_initialIndices hL S r]
      exact ⟨p, hp, rfl⟩
    obtain ⟨hpCollision, _a, _d, _hdp⟩ := hp.2
    have hs :
        (⟨p.start, (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.popularAuxiliaryInput hL.legal) S.cut r q})
              |>.starts_in_source hpCollision⟩ :
            (L.popularAuxiliaryInput hL.legal).lambda.source) =
        ⟨p.start, (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | L.assertion819StrictCollisionPath hL S r q})
              |>.starts_in_source hp⟩ := Subtype.ext rfl
    have haCollision : (L.popularAuxiliaryIndexed hL).f
        ⟨p.start, (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.popularAuxiliaryInput hL.legal) S.cut r q})
              |>.starts_in_source hpCollision⟩ ∈
          L.assertion819StrictCollisionIndices hL S r := by
      simpa only [hs] using ha
    obtain ⟨x, hx, hxp⟩ :=
      L.assertion819StrictCollision_meets_trace hL S r p
        hpCollision haCollision
    refine ⟨x, ?_, hxp⟩
    simpa only [hs] using hx
  fragmentIndices_nonstationary := HF.initialIndices_nonstationary

/-- If no strict owner exists, all owners are at the same stage as the
grounded source.  This is the precise matched-contact certificate. -/
structure Assertion819EqualMatch
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (a : Below kappa) where
  owner : L.Assertion819CollisionOwner hL S r a
  every_owner_stage_eq : ∀ d : L.Assertion819CollisionOwner hL S r a,
    L.hangingComponentStage hL.legal d.component
      d.component_mem d.component_hanging = a
  source_grounded : a ∈ L.phiGround

/-- Every grounded collision index is either strictly bad or all of its
contacts have the exact matched owner stage. -/
theorem assertion819_strict_or_equalMatch
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    {a : Below kappa} (ha : a ∈ L.assertion819CollisionIndices hL S r)
    (hground : a ∈ L.phiGround) :
    a ∈ L.assertion819StrictCollisionIndices hL S r ∨
      Nonempty (L.Assertion819EqualMatch hL S r a) := by
  by_cases hstrict : Nonempty (L.Assertion819StrictOwner hL S r a)
  · exact Or.inl hstrict
  · obtain ⟨d, _hd⟩ :=
      L.assertion819CollisionOwner?_eq_some_of_mem hL S r ha
    right
    refine ⟨⟨d, ?_, hground⟩⟩
    intro e
    rcases (L.hasAssertion819WeakChronology hL S r a e).lt_or_eq with hlt | heq
    · exact False.elim (hstrict ⟨{ owner := e, stage_lt := hlt }⟩)
    · exact heq

/-- Decoder-facing form: a grounded literal collision which is not in the
strict bad path family has only matched equal-stage owners. -/
theorem assertion819EqualMatch_of_grounded_collision_of_not_strict
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : PopularGroundingBridge.Request
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph)
    (hp : p ∈ (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths)
    (hground : (L.popularAuxiliaryIndexed hL).f
      ⟨p.start, (PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.popularAuxiliaryInput hL.legal) S.cut r q})
          |>.starts_in_source hp⟩ ∈ L.phiGround)
    (hnot : ¬ L.assertion819StrictCollisionPath hL S r p) :
    Nonempty (L.Assertion819EqualMatch hL S r
      ((L.popularAuxiliaryIndexed hL).f
        ⟨p.start, (PopularSwitching.restrictPaths
          (PopularGroundingBridge.requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.popularAuxiliaryInput hL.legal) S.cut r q})
            |>.starts_in_source hp⟩)) := by
  let a := (L.popularAuxiliaryIndexed hL).f
    ⟨p.start, (PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r q})
        |>.starts_in_source hp⟩
  have ha : a ∈ L.assertion819CollisionIndices hL S r :=
    ⟨p, hp, rfl⟩
  rcases L.assertion819_strict_or_equalMatch hL S r ha hground with
      hstrict | hequal
  · obtain ⟨d⟩ := hstrict
    apply False.elim
    apply hnot
    refine ⟨hp, a, d, ?_⟩
    let F := PopularSwitching.restrictPaths
      (PopularGroundingBridge.requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r q}
    have hpd := joinedFamily_path_eq_of_same_initialIndex
      (L.popularAuxiliaryIndexed hL)
      (L.popularAuxiliaryIndexed_sourceIndexed hL) F
      (PopularGroundingBridge.requestAuxVertex_not_mem_source r)
      hp d.owner.path_mem d.owner.index_eq.symm
    exact hpd.symm
  · exact hequal

end KappaLadder
end DWeb
end Erdos599
