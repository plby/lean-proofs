/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedRealization
import ErdosProblems.Erdos599.GroundingFiniteSourceRootAt

/-!
# Positive data behind a stopped-root obstruction

The full-boundary-stopped Assertion 8.22 compiler has only one abstract
failure mode: a point of `BB` is not reachable from an allowed original
source.  In the finite-source case that negative statement has a concrete
finite witness.  On the canonical grounded parent there is a last deleted
head, its surviving suffix ends at the boundary point, and the head itself
is still unrooted.  The incoming edge of that head is deleted for exactly
one of the four reasons listed by the erased decoder.

This is the finite datum required by the construction-specific exchange; no
global antichain or compatibility claim is made here.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- If an allowed root reaches the beginning of a finite path but not its
end, then a last deleted head exists and that head is itself unrooted. -/
theorem exists_unrootedLastDeletedHead
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
    · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet p.walk
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
    · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet
        D.suffix.walk
  exact D.suffix_finish ▸ (D.suffix_start ▸ hsuffix)

namespace Assertion822StoppedRootObstruction

/-- Rootedness predicate negated by a stopped-root obstruction. -/
def IsRooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822StoppedRootObstruction hL S R) : Prop :=
  ∃ a ∈ Gamma.source \ {R.record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ L.assertion822ReservedSwitchedEdgesAt
        hL S R (GroundingCut.BB
          (L.popularAuxiliaryInput hL.legal) S.cut)) a O.boundary

/-- Exact `BB` classification of a stranded stopped-relation point.  Each
branch retains the same non-rootedness certificate, so the downstream
exchange can work on finite sources, old requests, and blocking fragments
without reopening the image-set definition of `BL`. -/
theorem finiteSourceWithCut_or_oldRequestExit_or_blockingPoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822StoppedRootObstruction hL S R) :
    (O.boundary ∈ (L.popularAuxiliaryInput hL.legal).finiteSource ∧
      PopularAuxiliary.Input.LambdaVertex.old O.boundary ∈ S.cut ∧
      ¬ O.IsRooted) ∨
    ((∃ r : PopularGroundingBridge.Request
        (L.popularAuxiliaryInput hL.legal) S.cut,
      PopularGroundingBridge.requestAuxVertex r = .old O.boundary ∧
      GroundingErasedDecode.requestExit r = O.boundary) ∧
      ¬ O.IsRooted) ∨
    ((∃ P : (L.popularAuxiliaryInput hL.legal).Fragment,
      P ∈ GroundingCut.G0 (L.popularAuxiliaryInput hL.legal) S.cut ∧
      GroundingCut.IsBlockable
        (L.popularAuxiliaryInput hL.legal) S.cut P ∧
      GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary ∧
      O.boundary ∈ P.path.support) ∧
      ¬ O.IsRooted) := by
  rcases
      GroundingBBGeometry.mem_BB_finiteSourceWithCut_or_oldRequestExit_or_blockingPoint
        O.boundary_mem with hfinite | hold | hblocking
  · exact Or.inl ⟨hfinite.1, hfinite.2, O.not_rooted⟩
  · exact Or.inr (Or.inl ⟨hold, O.not_rooted⟩)
  · exact Or.inr (Or.inr ⟨hblocking, O.not_rooted⟩)

/-- The unrooted finite-source case of the stopped Assertion 8.22 relation
produces a canonical-parent last deleted head together with the exact
four-way deletion classification. -/
theorem exists_unrootedClassifiedLastDeletedHead_of_finiteSource
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822StoppedRootObstruction hL S R)
    (hfinite : O.boundary ∈
      (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hcut : PopularAuxiliary.Input.LambdaVertex.old O.boundary ∈ S.cut) :
    ∃ (p : FinitePath Gamma.graph)
        (_hchosen : L.chosen (L.finiteTerminalIndex ⟨O.boundary, hfinite⟩) =
          some (.inl p : Gamma.DPath))
        (D : LastDeletedHead p
          (L.assertion822ReservedSwitchedEdgesAt hL S R
            (GroundingCut.BB
              (L.popularAuxiliaryInput hL.legal) S.cut))),
      (¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedSwitchedEdgesAt hL S R
              (GroundingCut.BB
                (L.popularAuxiliaryInput hL.legal) S.cut)) a D.head) ∧
      ((∃ u, (u, D.head) ∈ p.edgeSet ∧
          (u, D.head) ∈ GroundingCut.CE
            (L.popularAuxiliaryInput hL.legal) S.cut) ∨
        (∃ u, (u, D.head) ∈ p.edgeSet ∧
          (u, D.head) ∈ erasedSelectedDirectionEdgesAt
            (L.popularAuxiliaryIndexed hL) S
              (L.reservedGroundedControls hL S R)
              (GroundingCut.BB
                (L.popularAuxiliaryInput hL.legal) S.cut) .backward) ∨
        (∃ u, (u, D.head) ∈ p.edgeSet ∧
          (u, D.head) ∈ forwardConflictCutEdgesAt
            (L.popularAuxiliaryIndexed hL) S
              (L.reservedGroundedControls hL S R)
              (GroundingCut.BB
                (L.popularAuxiliaryInput hL.legal) S.cut)) ∨
        (∃ u, (u, D.head) ∈ p.edgeSet ∧
          (u, D.head) ∈ residualLadderEdges
            (L.popularAuxiliaryIndexed hL) S ∧
          u ∈ GroundingCut.BB
            (L.popularAuxiliaryInput hL.legal) S.cut)) := by
  let T := GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut
  let E := L.assertion822ReservedSwitchedEdgesAt hL S R T
  obtain ⟨p, hchosen, hfinish, hsource, _hlimit, hrootNe⟩ :=
    R.exists_cutFiniteSource_parent_with_root_ne hfinite hcut
  have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start := by
    refine ⟨p.start, ⟨hsource, ?_⟩, .refl⟩
    simpa only [Set.mem_singleton_iff] using hrootNe.symm
  have hfinishNot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish := by
    rintro ⟨a, ha, hap⟩
    apply O.not_rooted
    exact ⟨a, ha, hfinish ▸ hap⟩
  obtain ⟨D, hDnot⟩ :=
    exists_unrootedLastDeletedHead p hstart hfinishNot
  refine ⟨p, hchosen, D, hDnot, ?_⟩
  exact classified_lastDeletedHead_of_recorded_finiteParentAt
    (L.reservedGroundedControls hL S R) T hchosen D

end Assertion822StoppedRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.exists_unrootedLastDeletedHead
#print axioms Erdos599.DWeb.KappaLadder.Assertion822StoppedRootObstruction.exists_unrootedClassifiedLastDeletedHead_of_finiteSource
