/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingActiveRequestRootTransfer
import ErdosProblems.Erdos599.GroundingPreStoppedRealization
import ErdosProblems.Erdos599.GroundingReservedBackwardOwner

/-!
# Root anchors of an active pre-stopped request

Before boundary stopping, every forward edge of an active erased request is
retained.  The finite alternating-root lemma therefore reduces failure to
root either its request exit or one of its forward vertices to one of the
actual route anchors: the decoded initial vertex, or the ambient start of a
backward link.  For the reserved controls the latter link has a limiting
ladder owner different from the reserved record.

These are lossless reductions.  They do not claim that the anchors already
survive the simultaneous switch.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingErasedDecode

open DirectedPath Alternating PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- In the pre-stopped relation, an active request exit is reached from its
decoded initial vertex or from the ambient start of one of its backward
links.  No separate forward-survival hypothesis is needed at `T = ∅`. -/
theorem activeRequestAt_empty_initial_or_backwardOwner_reaches_exit
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ActiveControlRequestAt U S K (∅ : Set V)) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
        (selectedRequestTrace U S K (chosenRequest c.1)).initial
        (requestExit (chosenRequest c.1)) ∨
      ∃ (l : Link Gamma.graph),
        l ∈ (selectedErasedCompression U S K
          (chosenRequest c.1)).path.links ∧
        l.direction = .backward ∧
        ∃ parent ∈ L.ladder.paths, l.path.IsSubpathOf parent ∧
          Relation.ReflTransGen
            (fun x y ↦
              (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
            l.path.start (requestExit (chosenRequest c.1)) := by
  let r := chosenRequest c.1
  let Tr := selectedRequestTrace U S K r
  let C := selectedErasedCompression U S K r
  cases hpath : C.path with
  | trivial v =>
      left
      have hi : v = Tr.initial := by
        have h := C.initial_eq
        rw [hpath] at h
        exact h
      have ht : v = requestExit r := by
        have h := C.terminal_eq
        rw [hpath] at h
        exact Option.some.inj h
      rw [← hi, ← ht]
  | finite Q =>
      have hback : BackwardLinksOn L.ladder.paths (.finite Q) := by
        simpa only [C, hpath] using
          selectedErasedCompression_backwardLinksOn U S K r
      have hforward : (AltPath.finite Q).directionEdges .forward ⊆
          erasedSelectedSwitchedEdgesAt U S K ∅ := by
        intro e he
        apply activeRetainedForwardEdgesAt_subset_switched U S K ∅ c
        rw [retainedForwardEdgesAt_empty]
        change e ∈ C.path.directionEdges .forward
        rw [hpath]
        exact he
      rcases Q.initial_or_backwardOwner_reaches_terminal hback hforward with
          hreach | ⟨l, hl, hldir, parent, hparent, hsub, hreach⟩
      · left
        have hi : Q.initial = Tr.initial := by
          have h := C.initial_eq
          rw [hpath] at h
          exact h
        have ht : Q.terminal = requestExit r := by
          have h := C.terminal_eq
          rw [hpath] at h
          exact Option.some.inj h
        simpa only [r, hi, ht] using hreach
      · right
        have ht : Q.terminal = requestExit r := by
          have h := C.terminal_eq
          rw [hpath] at h
          exact Option.some.inj h
        refine ⟨l, ?_, hldir, parent, hparent, hsub, ?_⟩
        · simpa only [C, hpath] using hl
        · simpa only [r, ht] using hreach
  | infinite Q =>
      have h := C.terminal_eq
      rw [hpath] at h
      simp at h

/-- Contrapositive anchor classification for an unrooted active request
exit in the pre-stopped relation. -/
theorem activeRequestAt_empty_exit_unrooted_cases
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ActiveControlRequestAt U S K (∅ : Set V))
    (A : Set V)
    (hnot : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
      a (requestExit (chosenRequest c.1))) :
    (¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
      a (selectedRequestTrace U S K (chosenRequest c.1)).initial) ∨
      ∃ (l : Link Gamma.graph) (parent : Gamma.DPath),
        l ∈ (selectedErasedCompression U S K
          (chosenRequest c.1)).path.links ∧
        l.direction = .backward ∧ parent ∈ L.ladder.paths ∧
        l.path.IsSubpathOf parent ∧
        ¬ ∃ a ∈ A, Relation.ReflTransGen
          (fun x y ↦
            (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
          a l.path.start := by
  rcases activeRequestAt_empty_initial_or_backwardOwner_reaches_exit
      U S K c with hinitial | ⟨l, hl, hldir, parent, hparent, hsub, hreach⟩
  · left
    rintro ⟨a, ha, haroot⟩
    exact hnot ⟨a, ha, haroot.trans hinitial⟩
  · right
    refine ⟨l, parent, hl, hldir, hparent, hsub, ?_⟩
    rintro ⟨a, ha, haroot⟩
    exact hnot ⟨a, ha, haroot.trans hreach⟩

/-- Contrapositive anchor classification for an unrooted forward vertex of
an active request. -/
theorem activeRequestAt_empty_forwardVertex_unrooted_cases
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ActiveControlRequestAt U S K (∅ : Set V))
    (A : Set V) {x : V}
    (hx : x ∈ (selectedErasedCompression U S K
      (chosenRequest c.1)).path.directionVertices .forward)
    (hnot : ¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
      a x) :
    (¬ ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
      a (selectedRequestTrace U S K (chosenRequest c.1)).initial) ∨
      ∃ (l : Link Gamma.graph) (parent : Gamma.DPath),
        l ∈ (selectedErasedCompression U S K
          (chosenRequest c.1)).path.links ∧
        l.direction = .backward ∧ parent ∈ L.ladder.paths ∧
        l.path.IsSubpathOf parent ∧
        ¬ ∃ a ∈ A, Relation.ReflTransGen
          (fun u v ↦
            (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
          a l.path.start := by
  classical
  by_cases hinitial : ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdgesAt U S K ∅)
      a (selectedRequestTrace U S K (chosenRequest c.1)).initial
  · right
    by_contra hback
    push_neg at hback
    apply hnot
    exact activeRequestAt_empty_forwardVertex_rooted_of_anchor_reachability
      U S K c hinitial (by
        intro l hl hldir parent hparent hsub
        exact hback l parent hl hldir hparent hsub) hx
  · exact Or.inl hinitial

end GroundingErasedDecode

namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Reserved-control specialization of the active-exit classification.  A
backward anchor is returned together with its certified non-reserved owner. -/
theorem UnusedGroundedRecord.reservedActiveRequest_exit_unrooted_cases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (c : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
        a (requestExit (chosenRequest c.1))) :
    (¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
        a (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest c.1)).initial) ∨
      ∃ (l : Link Gamma.graph) (parent : Gamma.DPath),
        l ∈ (selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest c.1)).path.links ∧
        l.direction = .backward ∧ parent ∈ L.limitWarp ∧
        l.path.IsSubpathOf parent ∧ parent ≠ R.record ∧
        ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦
              (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
            a l.path.start := by
  rcases activeRequestAt_empty_exit_unrooted_cases
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) c
      (Gamma.source \ {R.record.initial}) hnot with
      hinitial | ⟨l, parent, hl, hldir, hparent, hsub, hstart⟩
  · exact Or.inl hinitial
  · right
    have hparent' : parent ∈ L.limitWarp := hparent
    have hne : parent ≠ R.record :=
      R.backwardLink_parent_ne_record (chosenRequest c.1) l hl hldir
        parent hparent' hsub
    exact ⟨l, parent, hl, hldir, hparent', hsub, hne, hstart⟩

/-- Reserved-control specialization for an unrooted active forward vertex. -/
theorem UnusedGroundedRecord.reservedActiveRequest_forwardVertex_unrooted_cases
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (c : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    {x : V}
    (hx : x ∈ (selectedErasedCompression
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest c.1)).path.directionVertices .forward)
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
        a x) :
    (¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
        a (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest c.1)).initial) ∨
      ∃ (l : Link Gamma.graph) (parent : Gamma.DPath),
        l ∈ (selectedErasedCompression (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest c.1)).path.links ∧
        l.direction = .backward ∧ parent ∈ L.limitWarp ∧
        l.path.IsSubpathOf parent ∧ parent ≠ R.record ∧
        ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun u v ↦
              (u, v) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
            a l.path.start := by
  rcases activeRequestAt_empty_forwardVertex_unrooted_cases
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) c
      (Gamma.source \ {R.record.initial}) hx hnot with
      hinitial | ⟨l, parent, hl, hldir, hparent, hsub, hstart⟩
  · exact Or.inl hinitial
  · right
    have hparent' : parent ∈ L.limitWarp := hparent
    have hne : parent ≠ R.record :=
      R.backwardLink_parent_ne_record (chosenRequest c.1) l hl hldir
        parent hparent' hsub
    exact ⟨l, parent, hl, hldir, hparent', hsub, hne, hstart⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.GroundingErasedDecode.activeRequestAt_empty_initial_or_backwardOwner_reaches_exit
#print axioms
  Erdos599.GroundingErasedDecode.activeRequestAt_empty_exit_unrooted_cases
#print axioms
  Erdos599.GroundingErasedDecode.activeRequestAt_empty_forwardVertex_unrooted_cases
#print axioms
  Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.reservedActiveRequest_exit_unrooted_cases
#print axioms
  Erdos599.DWeb.KappaLadder.UnusedGroundedRecord.reservedActiveRequest_forwardVertex_unrooted_cases
