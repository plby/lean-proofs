/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingBackwardNormalization
import ErdosProblems.Erdos599.GroundingActiveRequestRootTransfer

/-!
# Active-control roots or normalized fresh-avoiding failures

Every active request exit is reached from its selected trace initial or from
the ambient start of one selected backward link.  The fresh-avoiding source
prefixes and the well-founded backward normalization therefore give a total
root-or-positive-failure theorem for each active control.
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
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev FreshActiveInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev FreshActiveIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev FreshActiveControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev FreshActiveRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev FreshActiveEdges :=
  L.splitGroundedFreshAvoidingCanonicalEdges hL hground hnotFresh S

/-- Pre-stopped active routes retain every forward edge, so their exit is
reachable from their decoded initial or from a genuine backward-link owner. -/
theorem splitGroundedFreshAvoiding_active_initial_or_backward_reaches_exit
    (c : ActiveControlRequestAt
      (FreshActiveIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshActiveControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshActiveEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (selectedRequestTrace
          (FreshActiveIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshActiveControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (chosenRequest c.1)).initial
        (requestExit (chosenRequest c.1)) ∨
      ∃ (l : Link Gamma.graph),
        l ∈ (selectedErasedCompression
          (FreshActiveIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshActiveControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (chosenRequest c.1)).path.links ∧
        l.direction = .backward ∧
        ∃ parent ∈ (FreshActiveInput (L := L) (hL := hL)).ladder.paths,
          l.path.IsSubpathOf parent ∧
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ FreshActiveEdges
              (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S))
            l.path.start (requestExit (chosenRequest c.1)) := by
  let U := FreshActiveIndexed (L := L) (hL := hL) (hground := hground)
  let K := FreshActiveControls (L := L) (hL := hL) (hground := hground)
    (hnotFresh := hnotFresh) (S := S)
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
      have hback : BackwardLinksOn
          (FreshActiveInput (L := L) (hL := hL)).ladder.paths (.finite Q) := by
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

/-- The decoded initial of one active request is rooted from an allowed
original source, or its failure has already been backward-normalized. -/
theorem splitGroundedFreshAvoiding_activeInitial_rooted_or_normalized
    (c : ActiveControlRequestAt
      (FreshActiveIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshActiveControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅) :
    (∃ a ∈ Gamma.source \ {
        (FreshActiveRecord (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)).record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshActiveEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a
        (selectedRequestTrace
          (FreshActiveIndexed (L := L) (hL := hL) (hground := hground)) S
          (FreshActiveControls (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S))
          (chosenRequest c.1)).initial) ∨
      L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) := by
  by_cases hroot : ∃ a ∈ Gamma.source \ {
      (FreshActiveRecord (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)).record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ FreshActiveEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a
      (selectedRequestTrace
        (FreshActiveIndexed (L := L) (hL := hL) (hground := hground)) S
        (FreshActiveControls (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S))
        (chosenRequest c.1)).initial
  · exact Or.inl hroot
  · right
    let data := Classical.choice
      (L.exists_splitGroundedFreshAvoidingInitialDeletedData
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) (chosenRequest c.1) hroot)
    exact (data.toRootState c).normalizeBackward

/-- Total active-control result: its actual control vertex is rooted in the
canonical pre-stopped relation, or a concrete normalized exchange/cut leaf
has been produced. -/
theorem splitGroundedFreshAvoiding_activeControl_rooted_or_normalized
    (c : ActiveControlRequestAt
      (FreshActiveIndexed (L := L) (hL := hL) (hground := hground)) S
      (FreshActiveControls (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) ∅) :
    (∃ a ∈ Gamma.source \ {
        (FreshActiveRecord (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)).record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ FreshActiveEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a c.1) ∨
      L.SplitGroundedFreshAvoidingBackwardNormalizedOutcome
        (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S) := by
  by_cases hroot : ∃ a ∈ Gamma.source \ {
      (FreshActiveRecord (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)).record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ FreshActiveEdges
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S)) a c.1
  · exact Or.inl hroot
  · right
    rcases L.splitGroundedFreshAvoiding_active_initial_or_backward_reaches_exit
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) c with hinitial | ⟨l, hl, hldir, parent, hparent, hsub, hreach⟩
    · have hinitialNot : ¬ ∃ a ∈ Gamma.source \ {
          (FreshActiveRecord (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)).record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ FreshActiveEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a
          (selectedRequestTrace
            (FreshActiveIndexed (L := L) (hL := hL) (hground := hground)) S
            (FreshActiveControls (L := L) (hL := hL) (hground := hground)
              (hnotFresh := hnotFresh) (S := S))
            (chosenRequest c.1)).initial := by
        rintro ⟨a, ha, haroot⟩
        apply hroot
        refine ⟨a, ha, haroot.trans ?_⟩
        simpa only [requestExit_chosenRequest] using hinitial
      let data := Classical.choice
        (L.exists_splitGroundedFreshAvoidingInitialDeletedData
          (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) (chosenRequest c.1) hinitialNot)
      exact (data.toRootState c).normalizeBackward
    · have hstartNot : ¬ ∃ a ∈ Gamma.source \ {
          (FreshActiveRecord (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)).record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ FreshActiveEdges
            (L := L) (hL := hL) (hground := hground)
            (hnotFresh := hnotFresh) (S := S)) a l.path.start := by
        rintro ⟨a, ha, haroot⟩
        apply hroot
        refine ⟨a, ha, haroot.trans ?_⟩
        simpa only [requestExit_chosenRequest] using hreach
      have hparentLimit : parent ∈ L.limitWarp := by
        simpa only [splitGroundedPopularAuxiliaryInput, limitWarp]
          using hparent
      let data := Classical.choice
        (L.exists_splitGroundedFreshAvoidingBackwardDeletedData
          (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) (chosenRequest c.1) l hl hldir parent
          hparentLimit hsub hstartNot)
      exact (data.toRootState c l hl hldir parent hsub).normalizeBackward

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedFreshAvoiding_activeControl_rooted_or_normalized
