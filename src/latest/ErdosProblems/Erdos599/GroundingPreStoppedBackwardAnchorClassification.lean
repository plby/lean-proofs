/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedActiveInitialClassification
import ErdosProblems.Erdos599.GroundingSelectedOwnerRank

/-!
# Classification of an unrooted active backward anchor

A backward anchor of an active reserved request lies on one limiting-ladder
parent different from the reserved record.  If that parent is grounded, its
initial segment to the anchor starts at an allowed original source, so an
unrooted anchor has a last deleted head with the exact pre-stopped deletion
classification.  A parent need not be grounded: the successor-corrected
Assertion 8.19 selector deliberately retains equal-stage hanging contacts.
In that case we return the genuine `Assertion819EqualMatch` certificate
instead of asserting a false source-prefix conclusion.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath Alternating PopularGroundingBridge
open PopularAuxiliary.Input GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- Positive finite data behind an unrooted backward-owner anchor when its
limiting-ladder owner is grounded. -/
structure ReservedBackwardOwnerLastDeletedHeadData
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    (l : Link Gamma.graph) (parent : Gamma.DPath) where
  parent_mem : parent ∈ L.limitWarp
  parent_grounded : PopularAuxiliary.IsGroundedPath Gamma parent
  parent_ne_reserved : parent ≠ R.record
  rootPath : FinitePath Gamma.graph
  rootPath_start : rootPath.start ∈ Gamma.source \ {R.record.initial}
  rootPath_finish : rootPath.finish = l.path.start
  rootPath_support : rootPath.support ⊆ parent.support
  rootPath_edges : rootPath.edgeSet ⊆ parent.edgeSet
  deleted : LastDeletedHead rootPath
    (L.assertion822ReservedPreStoppedEdges hL S R)
  deleted_head_not_rooted : ¬ ∃ a ∈
    Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R)
        a deleted.head
  deleted_class :
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ GroundingCut.CE
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ erasedSelectedDirectionEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅ .backward) ∨
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ forwardConflictCutEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅)

/-- The grounded parent supplying an active selected trace initial is one of
the limiting-ladder components exposed by that same selected auxiliary
path.  This follows from the actual erased-compression initial, not from a
raw decoded edge over-approximation. -/
theorem ReservedActiveInitialLastDeletedHeadData.parent_exposed
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)}
    (data : ReservedActiveInitialLastDeletedHeadData d) :
    data.parent ∈ exposedLadderPaths
      (L.popularAuxiliaryInput hL.legal)
      (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (chosenRequest d.1)) := by
  let E := selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) (chosenRequest d.1)
  have hpStart : (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (chosenRequest d.1)).start ∈
      (L.popularAuxiliaryInput hL.legal).lambda.source :=
    (strongSelectedWarp (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)).starts_in_source
        ⟨chosenRequest d.1, rfl⟩
  have hinitialCarrier :
      (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest d.1)).initial ∈
      (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier
        (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) (chosenRequest d.1)) := by
    apply GroundingErasedCarrierRank.selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (chosenRequest d.1)
    exact Set.mem_of_eq_of_mem E.initial_eq.symm
      E.path.initial_mem_vertexSet
  have hinitialParent :
      (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest d.1)).initial ∈ data.parent.support := by
    rw [← data.rootPath_finish]
    exact data.rootPath_support data.rootPath.finish_mem_support
  apply (L.popularAuxiliaryInput hL.legal).mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
    (L.popularAuxiliary_proxyPathsFaithful hL)
    (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (chosenRequest d.1))
    hpStart data.parent_inessential.1 hinitialCarrier hinitialParent

/-- The owner of a concrete backward link is exposed by the selected path
which contains that link.  This is the backward-anchor counterpart of
`ReservedActiveInitialLastDeletedHeadData.parent_exposed`. -/
theorem ReservedBackwardOwnerLastDeletedHeadData.parent_exposed
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
    parent ∈ exposedLadderPaths
      (L.popularAuxiliaryInput hL.legal)
      (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (chosenRequest d.1)) := by
  have hnonempty : l.path.edgeSet.Nonempty := by
    obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        l.path l.path.start_mem_support l.nontrivial
    exact ⟨(l.path.start, y), hy⟩
  obtain ⟨e, heLink⟩ := hnonempty
  have heDirection : e ∈ (selectedErasedCompression
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest d.1)).path.directionEdges .backward := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, heLink⟩
  have hePath :=
    (selectedBackwardEdge_auxContact_offApex
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest d.1) heDirection).1
  left
  refine ⟨?_, LambdaVertex.edge e.1 e.2, hePath,
    Or.inr ⟨e, hsub.2 heLink, rfl⟩⟩
  simpa only [KappaLadder.popularAuxiliaryInput] using data.parent_mem

/-- Named root-assumption-free outcomes for a deleted edge on the component
exposed by an active request. -/
inductive ExposedDeletedOwnerRankOutcome
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (c : ActiveControlRequestAt U S K ∅)
    (Y : Gamma.DPath) {p : FinitePath Gamma.graph}
    (D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt U S K ∅)) : Prop
  | cut
      (u : V) (parent_edge : (u, D.head) ∈ p.edgeSet)
      (cut_edge : (u, D.head) ∈ GroundingCut.CE J S.cut)
  | backward
      (u : V) (d : ActiveControlRequestAt U S K ∅)
      (l : Link Gamma.graph) (parent : Gamma.DPath)
      (parent_edge : (u, D.head) ∈ p.edgeSet)
      (selected_edge : (u, D.head) ∈
        erasedSelectedDirectionEdgesAt U S K ∅ .backward)
      (link_mem : l ∈ (selectedErasedCompression U S K
        (chosenRequest d.1)).path.links)
      (direction : l.direction = .backward)
      (link_edge : (u, D.head) ∈ l.path.edgeSet)
      (parent_mem : parent ∈ J.ladder.paths)
      (subpath : l.path.IsSubpathOf parent)
      (parent_eq : parent = Y)
      (owner_rank : d.1 = c.1 ∨
        controlRank U S d.1 < controlRank U S c.1)
  | forwardTail
      (u : V) (d : ActiveControlRequestAt U S K ∅) (f : V × V)
      (parent_edge : (u, D.head) ∈ p.edgeSet)
      (conflict : (u, D.head) ∈ forwardConflictCutEdgesAt U S K ∅)
      (retained : f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression U S K (chosenRequest d.1)).path)
      (same_tail : u = f.1)
      (owner_rank : d.1 = c.1 ∨
        controlRank U S d.1 < controlRank U S c.1)
  | retainedHead
      (u : V) (d : ActiveControlRequestAt U S K ∅) (f : V × V)
      (parent_edge : (u, D.head) ∈ p.edgeSet)
      (conflict : (u, D.head) ∈ forwardConflictCutEdgesAt U S K ∅)
      (retained : f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression U S K (chosenRequest d.1)).path)
      (head_eq : D.head = f.2)

/-- Root-assumption-free owner orientation for a deleted edge on an exposed
component.  A forward conflict is split literally: a same-tail conflict has
a ranked active owner, while a same-head conflict exposes the retained head
which must be fed back to the active-anchor recursion. -/
theorem LastDeletedHead.exposed_deletedOwnerRank_or_retainedHead
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful J)
    (c : ActiveControlRequestAt U S K ∅)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths J
      (strongSelectedPath U S K (chosenRequest c.1)))
    {p : FinitePath Gamma.graph}
    (hpY : p.edgeSet ⊆ Y.edgeSet)
    (D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt U S K ∅))
    (hclass :
      (∃ u, (u, D.head) ∈ p.edgeSet ∧
        (u, D.head) ∈ GroundingCut.CE J S.cut) ∨
      (∃ u, (u, D.head) ∈ p.edgeSet ∧
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          U S K ∅ .backward) ∨
      (∃ u, (u, D.head) ∈ p.edgeSet ∧
        (u, D.head) ∈ forwardConflictCutEdgesAt U S K ∅)) :
    (∃ u, (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ GroundingCut.CE J S.cut) ∨
    (∃ (u : V) (d : ActiveControlRequestAt U S K ∅)
        (l : Link Gamma.graph) (parent : Gamma.DPath),
      (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ erasedSelectedDirectionEdgesAt
        U S K ∅ .backward ∧
      l ∈ (selectedErasedCompression U S K
        (chosenRequest d.1)).path.links ∧
      l.direction = .backward ∧ (u, D.head) ∈ l.path.edgeSet ∧
      parent ∈ J.ladder.paths ∧ l.path.IsSubpathOf parent ∧
      parent = Y ∧
      (d.1 = c.1 ∨ controlRank U S d.1 < controlRank U S c.1)) ∨
    (∃ (u : V) (d : ActiveControlRequestAt U S K ∅)
        (f : V × V),
      (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ forwardConflictCutEdgesAt U S K ∅ ∧
      f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression U S K
          (chosenRequest d.1)).path ∧
      u = f.1 ∧
      (d.1 = c.1 ∨ controlRank U S d.1 < controlRank U S c.1)) ∨
    ∃ (u : V) (d : ActiveControlRequestAt U S K ∅)
        (f : V × V),
      (u, D.head) ∈ p.edgeSet ∧
      (u, D.head) ∈ forwardConflictCutEdgesAt U S K ∅ ∧
      f ∈ retainedForwardEdgesAt ∅
        (selectedErasedCompression U S K
          (chosenRequest d.1)).path ∧
      D.head = f.2 := by
  rcases hclass with hCE | hbackward | hconflict
  · exact Or.inl hCE
  · right
    left
    obtain ⟨u, huParent, huBackward⟩ := hbackward
    obtain ⟨d, l, parent, hl, hldir, hel, hparent, hsub,
        hparentY, hrank⟩ :=
      selectedBackwardEdge_owner_eq_or_rank_lt_of_mem_exposedParent
        U S K ∅ hfaith c Y hY huBackward (hpY huParent)
    exact ⟨u, d, l, parent, huParent, huBackward, hl, hldir,
      hel, hparent, hsub, hparentY, hrank⟩
  · obtain ⟨u, huParent, huConflict⟩ := hconflict
    rcases huConflict with ⟨huResidual, f, hf, htail | hhead⟩
    · right
      right
      left
      simp only [erasedSelectedRetainedForwardEdgesAt,
        Set.mem_iUnion] at hf
      obtain ⟨d, hfd⟩ := hf
      have hrank :=
        sameTailForwardOwner_eq_or_rank_lt_of_mem_exposedParent
          U S K ∅ hfaith c d Y hY (hpY huParent) hfd htail
      exact ⟨u, d, f, huParent,
        ⟨huResidual, f, by
          simp only [erasedSelectedRetainedForwardEdgesAt,
            Set.mem_iUnion]
          exact ⟨d, hfd⟩,
          Or.inl htail⟩,
        hfd, htail, hrank⟩
    · right
      right
      right
      simp only [erasedSelectedRetainedForwardEdgesAt,
        Set.mem_iUnion] at hf
      obtain ⟨d, hfd⟩ := hf
      exact ⟨u, d, f, huParent,
        ⟨huResidual, f, by
          simp only [erasedSelectedRetainedForwardEdgesAt,
            Set.mem_iUnion]
          exact ⟨d, hfd⟩,
          Or.inr hhead⟩,
        hfd, hhead⟩

/-- Package the disjunctive owner orientation in its named outcome type. -/
theorem exposedDeletedOwnerRankOutcome
    {I : Type u}
    {J : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed J.lambda kappa}
    {S : Popular.PopularSeparator U}
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful J)
    (c : ActiveControlRequestAt U S K ∅)
    (Y : Gamma.DPath)
    (hY : Y ∈ exposedLadderPaths J
      (strongSelectedPath U S K (chosenRequest c.1)))
    {p : FinitePath Gamma.graph}
    (hpY : p.edgeSet ⊆ Y.edgeSet)
    (D : LastDeletedHead p
      (erasedSelectedSwitchedEdgesAt U S K ∅))
    (hclass :
      (∃ u, (u, D.head) ∈ p.edgeSet ∧
        (u, D.head) ∈ GroundingCut.CE J S.cut) ∨
      (∃ u, (u, D.head) ∈ p.edgeSet ∧
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          U S K ∅ .backward) ∨
      (∃ u, (u, D.head) ∈ p.edgeSet ∧
        (u, D.head) ∈ forwardConflictCutEdgesAt U S K ∅)) :
    ExposedDeletedOwnerRankOutcome K c Y D := by
  rcases Assertion822PreStoppedRootObstruction.LastDeletedHead.exposed_deletedOwnerRank_or_retainedHead
      K hfaith c Y hY hpY D hclass with
      ⟨u, he, hcut⟩ |
      ⟨u, d, l, parent, he, hselected, hl, hdir, hlink,
        hparent, hsub, hparentEq, hrank⟩ |
      ⟨u, d, f, he, hconflict, hf, htail, hrank⟩ |
      ⟨u, d, f, he, hconflict, hf, hhead⟩
  · exact .cut u he hcut
  · exact .backward u d l parent he hselected hl hdir hlink
      hparent hsub hparentEq hrank
  · exact .forwardTail u d f he hconflict hf htail hrank
  · exact .retainedHead u d f he hconflict hf hhead

/-- The exact owner-split proposition attached to one selected-initial
deleted-head certificate. -/
def ReservedActiveInitialLastDeletedHeadData.DeletedOwnerRankOrRetainedHead
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)}
    (data : ReservedActiveInitialLastDeletedHeadData d) : Prop :=
  ExposedDeletedOwnerRankOutcome
    (L.reservedGroundedControls hL S R) d data.parent data.deleted

/-- Construct the named owner split for a selected-initial prefix. -/
theorem ReservedActiveInitialLastDeletedHeadData.deletedOwnerRank_or_retainedHead
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)}
    (data : ReservedActiveInitialLastDeletedHeadData d) :
    data.DeletedOwnerRankOrRetainedHead :=
  exposedDeletedOwnerRankOutcome
    (L.reservedGroundedControls hL S R)
    (L.popularAuxiliary_proxyPathsFaithful hL) d data.parent
    data.parent_exposed data.rootPath_edges data.deleted
    data.deleted_class

/-- The exact owner-split proposition attached to the grounded-prefix branch
of a backward-anchor certificate. -/
def ReservedBackwardOwnerLastDeletedHeadData.DeletedOwnerRankOrRetainedHead
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)}
    {l : Link Gamma.graph} {parent : Gamma.DPath}
    (data : ReservedBackwardOwnerLastDeletedHeadData d l parent) : Prop :=
  ExposedDeletedOwnerRankOutcome
    (L.reservedGroundedControls hL S R) d parent data.deleted

/-- Construct the named owner split for a grounded backward-anchor prefix. -/
theorem ReservedBackwardOwnerLastDeletedHeadData.deletedOwnerRank_or_retainedHead
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
    data.DeletedOwnerRankOrRetainedHead :=
  exposedDeletedOwnerRankOutcome
    (L.reservedGroundedControls hL S R)
    (L.popularAuxiliary_proxyPathsFaithful hL) d parent
    (data.parent_exposed hl hldir hsub) data.rootPath_edges data.deleted
    data.deleted_class

/-- A reserved selected path meeting a hanging limiting-ladder component has
the exact equal-stage certificate from the successor-corrected Assertion
8.19 construction.  The reserved controls retain the same strict-collision
family as the grounded controls, so their additional record avoidance does
not affect this conclusion. -/
theorem UnusedGroundedRecord.reserved_hangingCollision_equalMatch
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    (hcollision : GroundingConcreteControls.hangingLadderCollision
      (L.popularAuxiliaryInput hL.legal) S.cut r
        (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) r)) :
    let p := strongSelectedPath (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r
    let hp : p.start ∈
        (L.popularAuxiliaryInput hL.legal).lambda.source :=
      (strongSelectedWarp (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)).starts_in_source ⟨r, rfl⟩
    Nonempty (L.Assertion819EqualMatch hL S r
      ((L.popularAuxiliaryIndexed hL).f ⟨p.start, hp⟩)) := by
  dsimp only
  let p := strongSelectedPath (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) r
  have hpControlled := strongSelectedPath_mem_controlledRequestFan
    (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r
  let hpCollision : p ∈ (PopularSwitching.restrictPaths (requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths :=
    ⟨hpControlled.1.1, hcollision⟩
  obtain ⟨hpSource, hpGround⟩ :=
    strongSelectedPath_mem_groundedSourcePaths_reserved R r
  have hs :
      (⟨p.start,
        (PopularSwitching.restrictPaths (requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.popularAuxiliaryInput hL.legal) S.cut r q})
              |>.starts_in_source hpCollision⟩ :
          (L.popularAuxiliaryInput hL.legal).lambda.source) =
        ⟨p.start, hpSource⟩ := Subtype.ext rfl
  have hground :
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.start,
          (PopularSwitching.restrictPaths (requestFan S r)
            {q | GroundingConcreteControls.hangingLadderCollision
              (L.popularAuxiliaryInput hL.legal) S.cut r q})
                |>.starts_in_source hpCollision⟩ ∈ L.phiGround := by
    rw [congrArg (L.popularAuxiliaryIndexed hL).f hs]
    exact hpGround
  have hnotStrict : ¬ L.assertion819StrictCollisionPath hL S r p := by
    intro hstrict
    apply hpControlled.2
    left
    exact hstrict
  have hmatch := L.assertion819EqualMatch_of_grounded_collision_of_not_strict
    hL S r p hpCollision hground hnotStrict
  simpa only [congrArg (L.popularAuxiliaryIndexed hL).f hs] using hmatch

/-- Exact owner data in the hanging backward-link case.  In particular the
component which owns the given link, rather than merely some component met
by the selected path, has stage equal to the selected grounded source
index. -/
theorem exists_reservedBackwardOwner_equalStageData_of_hanging
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    (l : Link Gamma.graph) (parent : Gamma.DPath)
    (hl : l ∈ (selectedErasedCompression
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest d.1)).path.links)
    (hldir : l.direction = .backward)
    (hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent)
    (hhang : PopularAuxiliary.IsHangingPath Gamma parent) :
    ∃ (a : Stationary.Below kappa)
        (owner : L.Assertion819CollisionOwner hL S
          (chosenRequest d.1) a)
        (_equalData : L.Assertion819EqualMatch hL S
          (chosenRequest d.1) a),
      owner.path = strongSelectedPath
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) (chosenRequest d.1) ∧
        owner.component = parent ∧
        L.hangingComponentStage hL.legal owner.component
          owner.component_mem owner.component_hanging = a := by
  classical
  let r := chosenRequest d.1
  let p := strongSelectedPath (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) r
  have hpControlled := strongSelectedPath_mem_controlledRequestFan
    (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r
  have hnonempty : l.path.edgeSet.Nonempty := by
    obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        l.path l.path.start_mem_support l.nontrivial
    exact ⟨(l.path.start, y), hy⟩
  obtain ⟨e, heLink⟩ := hnonempty
  have heDirection : e ∈ (selectedErasedCompression
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r).path.directionEdges
        .backward := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, by simpa only [r] using hl, hldir, heLink⟩
  obtain ⟨hePath, heOffApex⟩ :=
    selectedBackwardEdge_auxContact_offApex
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r heDirection
  have hcollision : GroundingConcreteControls.hangingLadderCollision
      (L.popularAuxiliaryInput hL.legal) S.cut r p := by
    refine ⟨parent, ⟨?_, hhang⟩,
      LambdaVertex.edge e.1 e.2, ?_, ?_⟩
    · simpa only [KappaLadder.popularAuxiliaryInput] using hparent
    · exact ⟨Or.inr ⟨e, hsub.2 heLink, rfl⟩, by
        simpa only [Set.mem_singleton_iff] using heOffApex⟩
    · simpa only [p] using hePath
  let hpCollision : p ∈ (PopularSwitching.restrictPaths (requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths :=
    ⟨hpControlled.1.1, hcollision⟩
  let a : Stationary.Below kappa :=
    (L.popularAuxiliaryIndexed hL).f
      ⟨p.start,
        (PopularSwitching.restrictPaths (requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.popularAuxiliaryInput hL.legal) S.cut r q})
              |>.starts_in_source hpCollision⟩
  let owner : L.Assertion819CollisionOwner hL S r a := {
    path := p
    path_mem := hpCollision
    index_eq := rfl
    component := parent
    component_mem := by
      simpa only [KappaLadder.popularAuxiliaryInput] using hparent
    component_hanging := hhang
    traceContact := LambdaVertex.edge e.1 e.2
    traceContact_mem_trace := Or.inr ⟨e, hsub.2 heLink, rfl⟩
    traceContact_ne_apex := heOffApex
    traceContact_mem_path := by simpa only [p] using hePath
    contact := e.1
    contact_mem_component :=
      (parent.edgeSet_subset_support_prod (hsub.2 heLink)).1
    traceContact_exit := rfl }
  obtain ⟨M⟩ :=
    UnusedGroundedRecord.reserved_hangingCollision_equalMatch R r hcollision
  have hpSource : p.start ∈
      (L.popularAuxiliaryInput hL.legal).lambda.source :=
    (strongSelectedWarp (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)).starts_in_source ⟨r, rfl⟩
  have hs :
      (⟨p.start,
        (PopularSwitching.restrictPaths (requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.popularAuxiliaryInput hL.legal) S.cut r q})
              |>.starts_in_source hpCollision⟩ :
          (L.popularAuxiliaryInput hL.legal).lambda.source) =
        ⟨p.start, hpSource⟩ := Subtype.ext rfl
  have hMa :
      L.Assertion819EqualMatch hL S r a := by
    simpa only [a, congrArg (L.popularAuxiliaryIndexed hL).f hs] using M
  exact ⟨a, owner, hMa, rfl, rfl, hMa.every_owner_stage_eq owner⟩

/-- An unrooted backward owner either has a grounded, nonreserved root
prefix with an exact last-deleted-edge class, or is one of the genuine
equal-stage hanging contacts retained by Assertion 8.19. -/
theorem exists_reservedBackwardOwnerLastDeletedHeadData_or_equalMatch
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    (l : Link Gamma.graph) (parent : Gamma.DPath)
    (hl : l ∈ (selectedErasedCompression
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest d.1)).path.links)
    (hldir : l.direction = .backward)
    (hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent)
    (hne : parent ≠ R.record)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R)
        a l.path.start) :
    Nonempty (ReservedBackwardOwnerLastDeletedHeadData d l parent) ∨
      let p := strongSelectedPath (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (chosenRequest d.1)
      let hp : p.start ∈
          (L.popularAuxiliaryInput hL.legal).lambda.source :=
        (strongSelectedWarp (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)).starts_in_source
            ⟨chosenRequest d.1, rfl⟩
      Nonempty (L.Assertion819EqualMatch hL S (chosenRequest d.1)
        ((L.popularAuxiliaryIndexed hL).f ⟨p.start, hp⟩)) := by
  classical
  by_cases hground : PopularAuxiliary.IsGroundedPath Gamma parent
  · left
    have hrootNe : parent.initial ≠ R.record.initial := by
      intro heq
      apply hne
      apply Alternating.DWeb.IsWarp.eq_of_mem_support
        (hL.legal.warpStages (Ladder.finalStage kappa))
        hparent R.limit_inessential.1
      · exact parent.initial_mem_support
      · rw [heq]
        exact R.record.initial_mem_support
    obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix parent
        (hsub.1 l.path.start_mem_support)
    have hqStartAllowed : q.start ∈
        Gamma.source \ {R.record.initial} := by
      rw [hqStart]
      exact ⟨hground, fun heq =>
        hrootNe (Set.mem_singleton_iff.mp heq)⟩
    have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R)
          a q.start := ⟨q.start, hqStartAllowed, .refl⟩
    have hfinish : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R)
          a q.finish := by
      intro hroot
      apply hnot
      simpa only [hqFinish] using hroot
    obtain ⟨D, hDnot⟩ :=
      exists_unrootedLastDeletedHead q hstart hfinish
    have hqFamily : q.edgeSet ⊆
        (L.popularAuxiliaryInput hL.legal).familyEdges := by
      intro e he
      refine ⟨parent, ?_, hqEdges he⟩
      simpa only [KappaLadder.popularAuxiliaryInput] using hparent
    have hclass := D.exists_classified_deletedIncomingPreStopped
      (L.reservedGroundedControls hL S R) hqFamily
    exact ⟨{
      parent_mem := hparent
      parent_grounded := hground
      parent_ne_reserved := hne
      rootPath := q
      rootPath_start := hqStartAllowed
      rootPath_finish := hqFinish
      rootPath_support := hqSupport
      rootPath_edges := hqEdges
      deleted := D
      deleted_head_not_rooted := hDnot
      deleted_class := hclass }⟩
  · right
    have hnonempty : l.path.edgeSet.Nonempty := by
      obtain ⟨y, hy⟩ :=
        _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          l.path l.path.start_mem_support l.nontrivial
      exact ⟨(l.path.start, y), hy⟩
    obtain ⟨e, heLink⟩ := hnonempty
    have heDirection : e ∈ (selectedErasedCompression
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest d.1)).path.directionEdges .backward := by
      simp only [AltPath.directionEdges, Set.mem_iUnion]
      exact ⟨l, hl, hldir, heLink⟩
    obtain ⟨hePath, heOffApex⟩ :=
      selectedBackwardEdge_auxContact_offApex
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R)
        (chosenRequest d.1) heDirection
    have hcollision : GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut (chosenRequest d.1)
        (strongSelectedPath (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) (chosenRequest d.1)) := by
      refine ⟨parent, ⟨?_, hground⟩,
        LambdaVertex.edge e.1 e.2, ?_, hePath⟩
      · simpa only [KappaLadder.popularAuxiliaryInput] using hparent
      · exact ⟨Or.inr ⟨e, hsub.2 heLink, rfl⟩, by
          simpa only [Set.mem_singleton_iff] using heOffApex⟩
    exact UnusedGroundedRecord.reserved_hangingCollision_equalMatch R
      (chosenRequest d.1) hcollision

end Assertion822PreStoppedRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.UnusedGroundedRecord.reserved_hangingCollision_equalMatch
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedActiveInitialLastDeletedHeadData.parent_exposed
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.ReservedBackwardOwnerLastDeletedHeadData.parent_exposed
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.LastDeletedHead.exposed_deletedOwnerRank_or_retainedHead
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.exists_reservedBackwardOwner_equalStageData_of_hanging
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.exists_reservedBackwardOwnerLastDeletedHeadData_or_equalMatch
