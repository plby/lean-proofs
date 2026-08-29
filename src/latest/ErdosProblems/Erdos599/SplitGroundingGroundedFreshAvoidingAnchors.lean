/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingCanonical
import ErdosProblems.Erdos599.SplitGroundingGroundedRootProvenance

/-!
# Root-anchor data for the fresh-avoiding grounded switch

In the branch in which the genuinely fresh grounded stages are
nonstationary, the canonical selector forbids every original hanging
component.  Consequently both kinds of anchors used by an active selected
request have literal finite prefixes from an allowed original source:
the decoded initial and the ambient start of every backward link.

This file turns an unrooted anchor into positive last-deleted-head data.
There is no equal-stage or hanging-provider alternative.  The three
displayed deletion classes are exactly the possible failures in the
pre-stopped relation.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedForwardConflict

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev FreshAnchorInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev FreshAnchorIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev FreshAnchorControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev FreshAnchorRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev FreshAnchorEdges :=
  L.splitGroundedFreshAvoidingCanonicalEdges hL hground hnotFresh S

private theorem exists_unrootedLastDeletedHead_freshAnchor
    {E : Set (V × V)} {A : Set V}
    (p : FinitePath Gamma.graph)
    (hstart : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start)
    (hfinish : ¬ ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish) :
    ∃ D : LastDeletedHead p E,
      ¬ ∃ a ∈ A,
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a D.head := by
  have hdeleted : ∃ e ∈ p.edgeSet, e ∉ E := by
    by_contra hnone
    apply hfinish
    obtain ⟨a, ha, hastart⟩ := hstart
    refine ⟨a, ha, hastart.trans ?_⟩
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ p.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      by_contra hxyE
      exact hnone ⟨(x, y), hxy, hxyE⟩
    · exact Alternating.Walk.reflTransGen_edgeSet p.walk
  let D := (exists_lastDeletedHead p hdeleted).some
  refine ⟨D, ?_⟩
  rintro ⟨a, ha, haD⟩
  apply hfinish
  refine ⟨a, ha, haD.trans ?_⟩
  have hsuffix : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) D.suffix.start D.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      exact D.suffix_edgeSet_subset hxy
    · exact Alternating.Walk.reflTransGen_edgeSet D.suffix.walk
  exact D.suffix_finish ▸ (D.suffix_start ▸ hsuffix)

/-- Positive finite data behind an unrooted selected trace initial in the
fresh-avoiding canonical relation. -/
structure SplitGroundedFreshAvoidingInitialDeletedData
    (r : Request (FreshAnchorInput (L := L) (hL := hL)) S.cut) where
  parent : Gamma.DPath
  parent_inessential : parent ∈ Gamma.inessentialPaths L.limitWarp
  rootPath : FinitePath Gamma.graph
  rootPath_start : rootPath.start ∈ Gamma.source \ {
    (FreshAnchorRecord (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)).record.initial}
  rootPath_finish : rootPath.finish =
    (selectedRequestTrace
      (FreshAnchorIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshAnchorControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) r).initial
  rootPath_support : rootPath.support ⊆ parent.support
  rootPath_edges : rootPath.edgeSet ⊆ parent.edgeSet
  deleted : LastDeletedHead rootPath
    (FreshAnchorEdges (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
  deleted_head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {
      (FreshAnchorRecord (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)).record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ FreshAnchorEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a deleted.head
  deleted_class :
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ GroundingCut.CE
        (FreshAnchorInput (L := L) (hL := hL)) S.cut) ∨
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ erasedSelectedDirectionEdgesAt
        (FreshAnchorIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshAnchorControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅ .backward) ∨
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ forwardConflictCutEdgesAt
        (FreshAnchorIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshAnchorControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)

/-- An unrooted selected trace initial has a concrete finite allowed-source
prefix and a classified last deleted edge. -/
theorem exists_splitGroundedFreshAvoidingInitialDeletedData
    (r : Request (FreshAnchorInput (L := L) (hL := hL)) S.cut)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {
        (FreshAnchorRecord (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)).record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshAnchorEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a
        (selectedRequestTrace
          (FreshAnchorIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshAnchorControls (L := L) (hL := hL)
            (hground := hground) (hnotFresh := hnotFresh) (S := S)) r).initial) :
    Nonempty (L.SplitGroundedFreshAvoidingInitialDeletedData
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh) r) := by
  let R := FreshAnchorRecord (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  obtain ⟨parent, q, hparent, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    R.exists_selectedRequest_allowedRootPrefix r
  let E := FreshAnchorEdges (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let A := Gamma.source \ {R.record.initial}
  have hstart : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a q.start :=
    ⟨q.start, hqStart, .refl⟩
  have hfinish : ¬ ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a q.finish := by
    intro hroot
    apply hnot
    simpa only [hqFinish] using hroot
  obtain ⟨D, hDnot⟩ :=
    exists_unrootedLastDeletedHead_freshAnchor q hstart hfinish
  have hqFamily : q.edgeSet ⊆
      (FreshAnchorInput (L := L) (hL := hL)).familyEdges := by
    intro e he
    exact ⟨parent, hparent.1, hqEdges he⟩
  have hclass := D.exists_classified_deletedIncomingAt_split
    (FreshAnchorControls (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) (∅ : Set V) hqFamily
  refine ⟨{
    parent := parent
    parent_inessential := hparent
    rootPath := q
    rootPath_start := hqStart
    rootPath_finish := hqFinish
    rootPath_support := hqSupport
    rootPath_edges := hqEdges
    deleted := D
    deleted_head_not_rooted := hDnot
    deleted_class := ?_ }⟩
  rcases hclass with hCE | hbackward | hconflict |
      ⟨u, _huParent, _huResidual, huEmpty⟩
  · exact Or.inl hCE
  · exact Or.inr (Or.inl hbackward)
  · exact Or.inr (Or.inr hconflict)
  · exact False.elim (by simpa using huEmpty)

/-- Positive finite data behind an unrooted selected backward owner in the
fresh-avoiding canonical relation. -/
structure SplitGroundedFreshAvoidingBackwardDeletedData
    (r : Request (FreshAnchorInput (L := L) (hL := hL)) S.cut)
    (l : Link Gamma.graph) (parent : Gamma.DPath) where
  parent_mem : parent ∈ L.limitWarp
  rootPath : FinitePath Gamma.graph
  rootPath_start : rootPath.start ∈ Gamma.source \ {
    (FreshAnchorRecord (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)).record.initial}
  rootPath_finish : rootPath.finish = l.path.start
  rootPath_support : rootPath.support ⊆ parent.support
  rootPath_edges : rootPath.edgeSet ⊆ parent.edgeSet
  deleted : LastDeletedHead rootPath
    (FreshAnchorEdges (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
  deleted_head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {
      (FreshAnchorRecord (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)).record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ FreshAnchorEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a deleted.head
  deleted_class :
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ GroundingCut.CE
        (FreshAnchorInput (L := L) (hL := hL)) S.cut) ∨
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ erasedSelectedDirectionEdgesAt
        (FreshAnchorIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshAnchorControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅ .backward) ∨
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ forwardConflictCutEdgesAt
        (FreshAnchorIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshAnchorControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) ∅)

/-- In the fresh-avoiding branch every unrooted backward owner has concrete
deleted-head data; the old equal-stage alternative is impossible by the
construction of the controls. -/
theorem exists_splitGroundedFreshAvoidingBackwardDeletedData
    (r : Request (FreshAnchorInput (L := L) (hL := hL)) S.cut)
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (FreshAnchorIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshAnchorControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) r).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {
        (FreshAnchorRecord (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)).record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshAnchorEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a l.path.start) :
    Nonempty (L.SplitGroundedFreshAvoidingBackwardDeletedData
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      r l parent) := by
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    L.splitGroundedFreshAvoidingCanonicalBackwardOwner_rootPrefix
      hL hground hnotFresh S r l hl hldir parent hparent hsub
  let R := FreshAnchorRecord (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let E := FreshAnchorEdges (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
  let A := Gamma.source \ {R.record.initial}
  have hstart : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a q.start :=
    ⟨q.start, hqStart, .refl⟩
  have hfinish : ¬ ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a q.finish := by
    intro hroot
    apply hnot
    simpa only [hqFinish] using hroot
  obtain ⟨D, hDnot⟩ :=
    exists_unrootedLastDeletedHead_freshAnchor q hstart hfinish
  have hqFamily : q.edgeSet ⊆
      (FreshAnchorInput (L := L) (hL := hL)).familyEdges := by
    intro e he
    refine ⟨parent, ?_, hqEdges he⟩
    simpa only [splitGroundedPopularAuxiliaryInput, limitWarp] using hparent
  have hclass := D.exists_classified_deletedIncomingAt_split
    (FreshAnchorControls (L := L) (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S)) (∅ : Set V) hqFamily
  refine ⟨{
    parent_mem := hparent
    rootPath := q
    rootPath_start := hqStart
    rootPath_finish := hqFinish
    rootPath_support := hqSupport
    rootPath_edges := hqEdges
    deleted := D
    deleted_head_not_rooted := hDnot
    deleted_class := ?_ }⟩
  rcases hclass with hCE | hbackward | hconflict |
      ⟨u, _huParent, _huResidual, huEmpty⟩
  · exact Or.inl hCE
  · exact Or.inr (Or.inl hbackward)
  · exact Or.inr (Or.inr hconflict)
  · exact False.elim (by simpa using huEmpty)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedFreshAvoidingInitialDeletedData
#print axioms
  Erdos599.DWeb.KappaLadder.exists_splitGroundedFreshAvoidingBackwardDeletedData
