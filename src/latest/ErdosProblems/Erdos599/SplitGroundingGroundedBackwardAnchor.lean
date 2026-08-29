/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedCanonicalSimultaneous
import ErdosProblems.Erdos599.GroundingFiniteSourceRootAt

/-!
# Canonical grounded backward-anchor normalization

The reserved controls exclude the omitted record from every selected
backward link.  A remaining backward owner therefore supplies either a
finite allowed-source prefix to the link anchor or the genuine equal-stage
hanging certificate.  If the anchor is not rooted in the pre-stopped
switch, the former alternative has a last deleted head, with exactly the
three possible pre-stopped deletion classes.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev GroundedAnchorInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev GroundedAnchorIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev GroundedAnchorControls :=
  L.splitGroundedCanonicalControls hL hground S

private abbrev GroundedAnchorEdges :=
  L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅

/-- Positive finite data exposed by an unrooted selected backward anchor.
The owner prefix begins at an allowed original source, and its last missing
edge is classified without any boundary-stopping alternative. -/
structure SplitGroundedCanonicalBackwardAnchorDeletedData
    (r : Request (GroundedAnchorInput (L := L) (hL := hL)) S.cut)
    (l : Link Gamma.graph) (parent : Gamma.DPath) where
  parent_mem : parent ∈ L.limitWarp
  rootPath : FinitePath Gamma.graph
  rootPath_start : rootPath.start ∈ Gamma.source \ {
    (L.splitGroundedCanonicalUnusedRecord hL hground S).record.initial}
  rootPath_finish : rootPath.finish = l.path.start
  rootPath_support : rootPath.support ⊆ parent.support
  rootPath_edges : rootPath.edgeSet ⊆ parent.edgeSet
  deleted : LastDeletedHead rootPath
    (GroundedAnchorEdges (L := L) (hL := hL)
      (hground := hground) (S := S))
  deleted_head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {
      (L.splitGroundedCanonicalUnusedRecord hL hground S).record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ GroundedAnchorEdges
        (L := L) (hL := hL) (hground := hground) (S := S))
      a deleted.head
  deleted_class :
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ GroundingCut.CE
        (GroundedAnchorInput (L := L) (hL := hL)) S.cut) ∨
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ erasedSelectedDirectionEdgesAt
        (GroundedAnchorIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (GroundedAnchorControls (L := L) (hL := hL)
          (hground := hground) (S := S)) ∅ .backward) ∨
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ forwardConflictCutEdgesAt
        (GroundedAnchorIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (GroundedAnchorControls (L := L) (hL := hL)
          (hground := hground) (S := S)) ∅)

private theorem exists_unrootedLastDeletedHead_groundedAnchor
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

/-- Canonical unrooted backward-anchor split.  The finite branch is fully
reduced to a last-deleted edge; the alternative retains the actual
successor-correct equal-stage certificate rather than replacing it by a
false grounded prefix. -/
theorem splitGroundedCanonicalBackwardAnchor_deletedData_or_equalMatch
    (r : Request (GroundedAnchorInput (L := L) (hL := hL)) S.cut)
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (GroundedAnchorIndexed (L := L) (hL := hL) (hground := hground)) S
      (GroundedAnchorControls (L := L) (hL := hL)
        (hground := hground) (S := S)) r).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hsub : l.path.IsSubpathOf parent)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {
        (L.splitGroundedCanonicalUnusedRecord hL hground S).record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ GroundedAnchorEdges
          (L := L) (hL := hL) (hground := hground) (S := S))
        a l.path.start) :
    Nonempty (L.SplitGroundedCanonicalBackwardAnchorDeletedData r l parent) ∨
    let p := strongSelectedPath
      (GroundedAnchorIndexed (L := L) (hL := hL) (hground := hground)) S
      (GroundedAnchorControls (L := L) (hL := hL)
        (hground := hground) (S := S)) r
    let hp : p.start ∈
        (GroundedAnchorInput (L := L) (hL := hL)).lambda.source :=
      (strongSelectedWarp
        (GroundedAnchorIndexed (L := L) (hL := hL) (hground := hground)) S
        (GroundedAnchorControls (L := L) (hL := hL)
          (hground := hground) (S := S))).starts_in_source ⟨r, rfl⟩
    Nonempty (L.SplitGroundedAssertion819EqualMatch hL hground S r
      ((GroundedAnchorIndexed (L := L) (hL := hL)
        (hground := hground)).f ⟨p.start, hp⟩)) := by
  classical
  rcases L.splitGroundedCanonicalBackwardOwner_rootPrefix_or_equalMatch
      hL hground S r l hl hldir parent hparent hsub with
      ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ | hmatch
  · left
    let E := GroundedAnchorEdges
      (L := L) (hL := hL) (hground := hground) (S := S)
    let A := Gamma.source \ {
      (L.splitGroundedCanonicalUnusedRecord hL hground S).record.initial}
    have hstart : ∃ a ∈ A,
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a q.start :=
      ⟨q.start, hqStart, .refl⟩
    have hfinish : ¬ ∃ a ∈ A,
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a q.finish := by
      intro hroot
      apply hnot
      simpa only [hqFinish] using hroot
    obtain ⟨D, hDnot⟩ :=
      exists_unrootedLastDeletedHead_groundedAnchor q hstart hfinish
    have hqFamily : q.edgeSet ⊆
        (GroundedAnchorInput (L := L) (hL := hL)).familyEdges := by
      intro e he
      refine ⟨parent, ?_, hqEdges he⟩
      simpa only [splitGroundedPopularAuxiliaryInput, limitWarp] using hparent
    have hclass := D.exists_classified_deletedIncomingAt_split
      (GroundedAnchorControls (L := L) (hL := hL)
        (hground := hground) (S := S)) (∅ : Set V) hqFamily
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
  · exact Or.inr hmatch

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedCanonicalBackwardAnchor_deletedData_or_equalMatch
