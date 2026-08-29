/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBackwardAnchor

/-!
# Grounded-owner specialization of canonical backward normalization

When the owner of a selected backward link is grounded, the genuine
equal-stage hanging alternative cannot occur.  This file records the
positive finite prefix and its first unrooted deleted head directly, so
downstream root recursions do not need to recover the groundedness hidden
by the general collision dichotomy.
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

private abbrev GroundedBackwardInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev GroundedBackwardIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev GroundedBackwardControls :=
  L.splitGroundedCanonicalControls hL hground S

private abbrev GroundedBackwardEdges :=
  L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅

private theorem exists_unrootedLastDeletedHead_groundedOwner
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

/-- An unrooted canonical backward anchor whose actual limiting-ladder
owner is grounded always exposes finite deleted-head data.  In particular,
the equal-stage hanging certificate of the general theorem is absent. -/
theorem splitGroundedCanonicalBackwardAnchor_deletedData_of_grounded
    (r : Request (GroundedBackwardInput (L := L) (hL := hL)) S.cut)
    (l : Link Gamma.graph)
    (hl : l ∈ (selectedErasedCompression
      (GroundedBackwardIndexed (L := L) (hL := hL)
        (hground := hground)) S
      (GroundedBackwardControls (L := L) (hL := hL)
        (hground := hground) (S := S)) r).path.links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hparentGrounded : PopularAuxiliary.IsGroundedPath Gamma parent)
    (hsub : l.path.IsSubpathOf parent)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {
        (L.splitGroundedCanonicalUnusedRecord hL hground S).record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ GroundedBackwardEdges
          (L := L) (hL := hL) (hground := hground) (S := S))
        a l.path.start) :
    Nonempty (L.SplitGroundedCanonicalBackwardAnchorDeletedData
      r l parent) := by
  classical
  let R := L.splitGroundedCanonicalUnusedRecord hL hground S
  have hparentNe : parent ≠ R.record :=
    splitGroundedSelectedBackwardLink_parent_ne_record
      R r l hl hldir parent hparent hsub
  have hrootNe : parent.initial ≠ R.record.initial := by
    intro heq
    apply hparentNe
    apply Alternating.DWeb.IsWarp.eq_of_mem_support
      (hL.legal.warpStages (Ladder.finalStage kappa)) hparent
      R.limit_inessential.1
    · exact parent.initial_mem_support
    · rw [heq]
      exact R.record.initial_mem_support
  obtain ⟨q, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix parent
      (hsub.1 l.path.start_mem_support)
  have hqStartAllowed : q.start ∈ Gamma.source \ {R.record.initial} := by
    rw [hqStart]
    exact ⟨hparentGrounded, fun heq ↦
      hrootNe (Set.mem_singleton_iff.mp heq)⟩
  let E := GroundedBackwardEdges
    (L := L) (hL := hL) (hground := hground) (S := S)
  let A := Gamma.source \ {R.record.initial}
  have hstart : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a q.start :=
    ⟨q.start, hqStartAllowed, .refl⟩
  have hfinish : ¬ ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a q.finish := by
    intro hroot
    apply hnot
    simpa only [hqFinish] using hroot
  obtain ⟨D, hDnot⟩ :=
    exists_unrootedLastDeletedHead_groundedOwner q hstart hfinish
  have hqFamily : q.edgeSet ⊆
      (GroundedBackwardInput (L := L) (hL := hL)).familyEdges := by
    intro e he
    refine ⟨parent, ?_, hqEdges he⟩
    simpa only [splitGroundedPopularAuxiliaryInput, limitWarp] using hparent
  have hclass := D.exists_classified_deletedIncomingAt_split
    (GroundedBackwardControls (L := L) (hL := hL)
      (hground := hground) (S := S)) (∅ : Set V) hqFamily
  refine ⟨{
    parent_mem := hparent
    rootPath := q
    rootPath_start := hqStartAllowed
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
  Erdos599.DWeb.KappaLadder.splitGroundedCanonicalBackwardAnchor_deletedData_of_grounded
