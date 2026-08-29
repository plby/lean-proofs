/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingInitialPrefixMeasure

/-!
# Well-founded normalization of self-owned backward root failures

The owner classification for an unrooted deleted head has an equality case:
the deleted edge belongs to a backward link of the very active request which
exposes the ambient ladder member.  If the start of that link is unrooted and
its owner is grounded, the canonical source prefix to the link start has a
new unrooted last deleted head.  This new head lies strictly before the old
one on the same ambient member.  Consequently repeated equality cases are
well-founded, even when the ambient member is a ray.

This file performs exactly that recursion.  Strictly earlier owners recurse
by the primary control-rank coordinate, while equal owners recurse by the
secondary position coordinate.  A backward anchor whose start is already
rooted is retained as positive switch data, and a same-tail forward conflict
is retained as an explicit exchange outcome: rooting its common tail does not
restore the competing deleted parent edge.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath Alternating
open GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- A concrete unrooted deleted-head problem on a finite prefix of a ladder
member exposed by an active request. -/
structure ReservedExposedRootState
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S} where
  control : ActiveControlRequestAt
    (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) (∅ : Set V)
  parent : Gamma.DPath
  rootPath : FinitePath Gamma.graph
  rootPath_support : rootPath.support ⊆ parent.support
  rootPath_edges : rootPath.edgeSet ⊆ parent.edgeSet
  deleted : LastDeletedHead rootPath
    (L.assertion822ReservedPreStoppedEdges hL S R)
  deleted_head_not_rooted : ¬ ∃ a ∈
    Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦
          (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
        a deleted.head
  recursion : ReservedExposedDeletedRootRecursionOutcome
    control parent deleted

/-- The deleted head is an actual point of the ambient exposed member. -/
theorem ReservedExposedRootState.deleted_head_mem
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (s : ReservedExposedRootState (R := R)) :
    s.deleted.head ∈ s.parent.support := by
  obtain ⟨u, hu, _⟩ := s.deleted.deleted_incoming
  exact s.rootPath_support
    (s.rootPath.edgeSet_subset_support_prod hu).2

/-- Forgetting the finite prefix gives the rank/position state used by the
well-founded order. -/
def ReservedExposedRootState.exposedPoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (s : ReservedExposedRootState (R := R)) :
    ActiveExposedPoint (L.reservedGroundedControls hL S R) where
  control := s.control
  parent := s.parent
  point := s.deleted.head
  point_mem := s.deleted_head_mem

/-- The recursion order on concrete prefix problems is the already proved
lexicographic active-control/path-position order. -/
def ReservedExposedRootState.Precedes
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S} :
    ReservedExposedRootState (R := R) →
      ReservedExposedRootState (R := R) → Prop :=
  ActiveExposedPoint.Precedes.onFun
    ReservedExposedRootState.exposedPoint

theorem ReservedExposedRootState.precedes_wellFounded
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S} :
    WellFounded (@ReservedExposedRootState.Precedes
      V Gamma kappa L hL S R) := by
  exact InvImage.wf ReservedExposedRootState.exposedPoint
    ActiveExposedPoint.precedes_wellFounded

/-- Every point of a finite subpath occurs no later than its terminal vertex
on the ambient directed path. -/
theorem finiteSubpath_mem_beforeEq_finish
    (P : Gamma.DPath) (q : FinitePath Gamma.graph)
    (hsub : q.IsSubpathOf P) {x : V} (hx : x ∈ q.support) :
    GroundingCut.BeforeEq P x q.finish := by
  let m : q.walk.Meets ({x} : Set V) :=
    ⟨x, hx, Set.mem_singleton x⟩
  let r := q.lastHit ({x} : Set V) m
  have hrStart : r.start = x := by
    exact Set.mem_singleton_iff.mp
      (q.lastHit_start_mem ({x} : Set V) m)
  have hrFinish : r.finish = q.finish := rfl
  have hrEdges : r.edgeSet ⊆ P.edgeSet :=
    (q.lastHit_edgeSet_subset ({x} : Set V) m).trans hsub.2
  have hxP : x ∈ P.support := hsub.1 hx
  have hrStartP : r.start ∈ P.support := by
    simpa only [hrStart] using hxP
  simpa only [hrStart, hrFinish] using
    walk_beforeEq_of_edgeSet_subset P r.walk hrStartP hrEdges

/-- A weakly earlier point followed by a strictly earlier point is strictly
earlier. -/
theorem before_of_beforeEq_before
    (P : Gamma.DPath) {x y z : V}
    (hxy : GroundingCut.BeforeEq P x y)
    (hyz : GroundingCut.Before P y z) :
    GroundingCut.Before P x z := by
  refine ⟨GroundingFragmentResidualOrder.beforeEq_trans hxy hyz.1, ?_⟩
  intro hxz
  apply hyz.2
  apply GroundingCutDecoder.beforeEq_antisymm hyz.1
  simpa only [hxz] using hxy

/-- The unrooted last deleted head of the canonical prefix to a backward
link start lies strictly before the old deleted head whenever the link owns
the old deletion. -/
theorem ReservedBackwardOwnerLastDeletedHeadData.deletedHead_before_oldHead
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)}
    {l : Link Gamma.graph} {parent : Gamma.DPath}
    (data : ReservedBackwardOwnerLastDeletedHeadData d l parent)
    {u z : V} (hsub : l.path.IsSubpathOf parent)
    (huz : (u, z) ∈ l.path.edgeSet) :
    GroundingCut.Before parent data.deleted.head z := by
  obtain ⟨v, hv, _⟩ := data.deleted.deleted_incoming
  have hheadPrefix : data.deleted.head ∈ data.rootPath.support :=
    (data.rootPath.edgeSet_subset_support_prod hv).2
  have hheadStart : GroundingCut.BeforeEq parent
      data.deleted.head l.path.start := by
    simpa only [data.rootPath_finish] using
      finiteSubpath_mem_beforeEq_finish parent data.rootPath
        ⟨data.rootPath_support, data.rootPath_edges⟩ hheadPrefix
  exact before_of_beforeEq_before parent hheadStart
    (backwardLink_start_before_deletedHead parent l hsub huz)

/-! ## Total elimination of repeated self-backward constructors -/

/-- Terminal outcomes after all unrooted grounded backward anchors have been
recursively expanded.  The recursion uses control rank first and position on
the exposed parent second, so it also absorbs strict lower-rank owners.
Same-tail forward conflicts remain explicit exchange data. -/
inductive BackwardSelfNormalizedRootOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S} : Prop
  | activeAnchor
      (state : ReservedExposedRootState (R := R))
      (failure : ReservedActiveAnchorFailure (R := R))
  | inactiveControl
      (state : ReservedExposedRootState (R := R))
      (q : ControlRequest (L.popularAuxiliaryInput hL.legal) S.cut)
      (data : InactivePreStoppedRootObstructionData S
        (L.reservedGroundedControls hL S R)
        (Gamma.source \ {R.record.initial}) q)
  | rootedBackwardOwner
      (state : ReservedExposedRootState (R := R))
      (u : V)
      (owner : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (link : Link Gamma.graph) (parent : Gamma.DPath)
      (parent_edge : (u, state.deleted.head) ∈ state.rootPath.edgeSet)
      (selected_edge : (u, state.deleted.head) ∈
        erasedSelectedDirectionEdgesAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) ∅ .backward)
      (link_mem : link ∈ (selectedErasedCompression
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest owner.1)).path.links)
      (direction : link.direction = .backward)
      (link_edge : (u, state.deleted.head) ∈ link.path.edgeSet)
      (parent_mem : parent ∈
        (L.popularAuxiliaryInput hL.legal).ladder.paths)
      (subpath : link.path.IsSubpathOf parent)
      (parent_eq : parent = state.parent)
      (owner_rank : owner.1 = state.control.1 ∨
        controlRank (L.popularAuxiliaryIndexed hL) S owner.1 <
          controlRank (L.popularAuxiliaryIndexed hL) S state.control.1)
      (rooted : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R)
          a link.path.start)
  | hangingEqualMatch
      (owner : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (certificate : OwnerClassifiedReservedActiveEqualMatch owner)
  | forwardTailExchange
      (state : ReservedExposedRootState (R := R))
      (owner : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (u : V) (f : V × V)
      (conflict : (u, state.deleted.head) ∈ forwardConflictCutEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅)
      (retained : f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest owner.1)).path)
      (same_tail : u = f.1)
      (owner_rank : owner.1 = state.control.1 ∨
        controlRank (L.popularAuxiliaryIndexed hL) S owner.1 <
          controlRank (L.popularAuxiliaryIndexed hL) S state.control.1)

/-- One well-founded normalization pass.  An unrooted grounded backward
anchor constructs a strictly smaller state: by control rank for a strict
owner, or by path position for a self owner.  `previous` recursively
normalizes that state. -/
private def normalizeBackwardSelfStep
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (state : ReservedExposedRootState (R := R))
    (previous : ∀ next : ReservedExposedRootState (R := R),
      ReservedExposedRootState.Precedes next state →
      BackwardSelfNormalizedRootOutcome (R := R)) :
    BackwardSelfNormalizedRootOutcome (R := R) := by
  cases hrec : state.recursion with
  | activeAnchor failure => exact .activeAnchor state failure
  | inactiveControl q data => exact .inactiveControl state q data
  | backwardOwner u d l parent hparentEdge hselectedEdge hl hldir
      hlink hparent hsub hparentEq hrank =>
      rcases hrank with heq | hlt
      · have hdc : d = state.control := Subtype.ext heq
        subst d
        subst parent
        by_cases hroot : ∃ a ∈ Gamma.source \ {R.record.initial},
            Relation.ReflTransGen
              (fun x y ↦ (x, y) ∈
                L.assertion822ReservedPreStoppedEdges hL S R)
              a l.path.start
        · exact .rootedBackwardOwner state u state.control l state.parent
            hparentEdge hselectedEdge hl hldir hlink hparent hsub rfl
            (Or.inl rfl) hroot
        · have hparentLimit : state.parent ∈ L.limitWarp := by
            simpa only [KappaLadder.popularAuxiliaryInput] using hparent
          have hparentNe : state.parent ≠ R.record :=
            R.backwardLink_parent_ne_record
              (chosenRequest state.control.1) l hl hldir state.parent
              hparentLimit hsub
          rcases exists_reservedBackwardOwnerLastDeletedHeadData_or_equalMatch
              state.control l state.parent hl hldir hparentLimit hsub
              hparentNe hroot with hdata | hmatch
          · let data := hdata.some
            let next : ReservedExposedRootState (R := R) := {
              control := state.control
              parent := state.parent
              rootPath := data.rootPath
              rootPath_support := data.rootPath_support
              rootPath_edges := data.rootPath_edges
              deleted := data.deleted
              deleted_head_not_rooted := data.deleted_head_not_rooted
              recursion := data.rootRecursionOutcome hl hldir hsub }
            have hbefore : GroundingCut.Before state.parent
                next.deleted.head state.deleted.head := by
              exact data.deletedHead_before_oldHead hsub hlink
            have hnext : next.Precedes state := by
              exact Prod.Lex.right _
                (pathPosition_lt_of_before state.parent hbefore)
            exact previous next hnext
          · exact .hangingEqualMatch state.control (by
              simpa only [OwnerClassifiedReservedActiveEqualMatch]
                using hmatch)
      · by_cases hroot : ∃ a ∈ Gamma.source \ {R.record.initial},
            Relation.ReflTransGen
              (fun x y ↦ (x, y) ∈
                L.assertion822ReservedPreStoppedEdges hL S R)
              a l.path.start
        · exact .rootedBackwardOwner state u d l parent hparentEdge
            hselectedEdge hl hldir hlink hparent hsub hparentEq
            (Or.inr hlt) hroot
        · have hparentLimit : parent ∈ L.limitWarp := by
            simpa only [KappaLadder.popularAuxiliaryInput] using hparent
          have hparentNe : parent ≠ R.record :=
            R.backwardLink_parent_ne_record
              (chosenRequest d.1) l hl hldir parent hparentLimit hsub
          rcases exists_reservedBackwardOwnerLastDeletedHeadData_or_equalMatch
              d l parent hl hldir hparentLimit hsub hparentNe hroot with
            hdata | hmatch
          · let data := hdata.some
            let next : ReservedExposedRootState (R := R) := {
              control := d
              parent := parent
              rootPath := data.rootPath
              rootPath_support := data.rootPath_support
              rootPath_edges := data.rootPath_edges
              deleted := data.deleted
              deleted_head_not_rooted := data.deleted_head_not_rooted
              recursion := data.rootRecursionOutcome hl hldir hsub }
            have hnext : next.Precedes state := by
              exact ActiveExposedPoint.precedes_of_controlRank_lt hlt
            exact previous next hnext
          · exact .hangingEqualMatch d (by
              simpa only [OwnerClassifiedReservedActiveEqualMatch]
                using hmatch)
  | forwardTailOwner u d f _parentEdge hconflict hf htail hrank =>
      exact .forwardTailExchange state d u f hconflict hf htail hrank

/-- Repeated self-owned backward expansion terminates by the lexicographic
control-rank/path-position order. -/
noncomputable def ReservedExposedRootState.normalizeBackwardSelf
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (state : ReservedExposedRootState (R := R)) :
    BackwardSelfNormalizedRootOutcome (R := R) :=
  WellFounded.fix ReservedExposedRootState.precedes_wellFounded
    (fun state previous ↦ normalizeBackwardSelfStep state previous) state

/-- Initial-prefix data embeds in the well-founded root-state recursion. -/
def ReservedActiveInitialLastDeletedHeadData.toExposedRootState
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)}
    (data : ReservedActiveInitialLastDeletedHeadData d) :
    ReservedExposedRootState (R := R) where
  control := d
  parent := data.parent
  rootPath := data.rootPath
  rootPath_support := data.rootPath_support
  rootPath_edges := data.rootPath_edges
  deleted := data.deleted
  deleted_head_not_rooted := data.deleted_head_not_rooted
  recursion := data.rootRecursionOutcome

/-- Grounded backward-anchor prefix data embeds in the same recursion. -/
def ReservedBackwardOwnerLastDeletedHeadData.toExposedRootState
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)}
    {l : Link Gamma.graph} {parent : Gamma.DPath}
    (data : ReservedBackwardOwnerLastDeletedHeadData d l parent)
    (hl : l ∈ (selectedErasedCompression
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest d.1)).path.links)
    (hldir : l.direction = .backward)
    (hsub : l.path.IsSubpathOf parent) :
    ReservedExposedRootState (R := R) where
  control := d
  parent := parent
  rootPath := data.rootPath
  rootPath_support := data.rootPath_support
  rootPath_edges := data.rootPath_edges
  deleted := data.deleted
  deleted_head_not_rooted := data.deleted_head_not_rooted
  recursion := data.rootRecursionOutcome hl hldir hsub

/-- The ordered inactive-control segment is a genuine finite subpath of its
exposed parent. -/
theorem InactivePreStoppedRootObstructionData.segment_support_subset_parent
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    {A : Set V} {c : ControlRequest J S.cut}
    (data : InactivePreStoppedRootObstructionData S K A c) :
    data.segment.support ⊆ data.parent.support := by
  intro x hx
  by_cases hxFinish : x = data.segment.finish
  · rw [hxFinish, data.segment_finish]
    rcases data.contact_before_control with
      ⟨_m, _n, _hcontact, hcontrol, _hmn⟩
    exact GroundingCut.occursAt_mem_support hcontrol
  · obtain ⟨y, hxy⟩ :=
      data.segment.walk.exists_outgoing_edge_of_mem_of_ne_finish
        hx hxFinish
    exact (data.parent.edgeSet_subset_support_prod
      (data.segment_edges hxy)).1

/-- Inactive-control deleted-head data embeds in the same well-founded
root-state recursion. -/
def InactivePreStoppedRootObstructionData.toExposedRootState
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {c : ControlRequest (L.popularAuxiliaryInput hL.legal) S.cut}
    (data : InactivePreStoppedRootObstructionData S
      (L.reservedGroundedControls hL S R)
      (Gamma.source \ {R.record.initial}) c) :
    ReservedExposedRootState (R := R) where
  control := data.absorber
  parent := data.parent
  rootPath := data.segment
  rootPath_support :=
    InactivePreStoppedRootObstructionData.segment_support_subset_parent data
  rootPath_edges := data.segment_edges
  deleted := data.deleted
  deleted_head_not_rooted := data.deleted_head_not_rooted
  recursion := inactiveControlRootRecursionOutcome data

/-- Active-anchor failure after every repeated grounded self-backward
deleted-head recursion has been normalized. -/
inductive BackwardSelfNormalizedReservedActiveAnchorFailure
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S} : Prop
  | initial
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (data : ReservedActiveInitialLastDeletedHeadData d)
      (normalized : BackwardSelfNormalizedRootOutcome (R := R))
  | backwardOwner
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (l : Link Gamma.graph) (parent : Gamma.DPath)
      (link_mem : l ∈ (selectedErasedCompression
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest d.1)).path.links)
      (backward : l.direction = .backward)
      (subpath : l.path.IsSubpathOf parent)
      (data : ReservedBackwardOwnerLastDeletedHeadData d l parent)
      (normalized : BackwardSelfNormalizedRootOutcome (R := R))
  | hangingEqualMatch
      (d : ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (∅ : Set V))
      (certificate : OwnerClassifiedReservedActiveEqualMatch d)

/-- Normalize the recursively owner-classified active-anchor outcome. -/
theorem RecursivelyOwnerClassifiedReservedActiveAnchorFailure.backwardSelfNormalized
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (failure : RecursivelyOwnerClassifiedReservedActiveAnchorFailure
      (R := R)) :
    BackwardSelfNormalizedReservedActiveAnchorFailure (R := R) := by
  cases failure with
  | initialDeleted d data _recursion =>
      exact .initial d data data.toExposedRootState.normalizeBackwardSelf
  | backwardOwnerDeleted d l parent hl hldir hsub data _recursion =>
      exact .backwardOwner d l parent hl hldir hsub data
        (data.toExposedRootState hl hldir hsub).normalizeBackwardSelf
  | hangingEqualMatch d certificate =>
      exact .hangingEqualMatch d certificate

end Assertion822PreStoppedRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedExposedRootState.precedes_wellFounded
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedBackwardOwnerLastDeletedHeadData.deletedHead_before_oldHead
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedExposedRootState.normalizeBackwardSelf
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.RecursivelyOwnerClassifiedReservedActiveAnchorFailure.backwardSelfNormalized
