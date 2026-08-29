/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteAlternatingRoot
import ErdosProblems.Erdos599.GroundingErasedDecode

/-!
# Terminal-root reduction for one active grounding request

This specializes the finite alternating root transfer to one active request
of the simultaneous Section 8 switch when its whole forward trace lies in
the retained first-boundary prefix.  Under that explicit hypothesis the
request exit is reachable either from the decoded trace initial or from the
ambient start of an actual backward link, together with its limiting ladder
owner.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingErasedDecode

open DirectedPath Alternating
open PopularAuxiliary.Input PopularGroundingBridge
open GroundingSimultaneousDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Every forward edge of one active request is present in the final global
active switched relation provided that it lies in the retained
first-boundary prefix. -/
theorem activeRequest_forwardEdges_subset_switchedEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ActiveControlRequest U S K)
    (hretained :
      (selectedErasedCompression U S K
          (chosenRequest c.1)).path.directionEdges .forward ⊆
        retainedForwardEdges (L := L) S.cut
          (selectedErasedCompression U S K
            (chosenRequest c.1)).path) :
    (selectedErasedCompression U S K
        (chosenRequest c.1)).path.directionEdges .forward ⊆
      erasedSelectedSwitchedEdges U S K := by
  intro e he
  exact activeRetainedForwardEdges_subset_switched U S K c
    (hretained he)

/-- Concrete last-backward-owner reduction for one active request.  The
left branch is the no-backward case.  The right branch exposes the exact
limiting-ladder owner whose initial prefix must be grounded by the global
Assertion 8.22 geometry. -/
theorem activeRequest_initial_or_backwardOwner_reaches_exit
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ActiveControlRequest U S K)
    (hretained :
      (selectedErasedCompression U S K
          (chosenRequest c.1)).path.directionEdges .forward ⊆
        retainedForwardEdges (L := L) S.cut
          (selectedErasedCompression U S K
            (chosenRequest c.1)).path) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K)
        (selectedRequestTrace U S K (chosenRequest c.1)).initial
        (requestExit (chosenRequest c.1)) ∨
      ∃ (l : Link Gamma.graph),
        l ∈ (selectedErasedCompression U S K
          (chosenRequest c.1)).path.links ∧
        l.direction = .backward ∧
        ∃ parent ∈ L.ladder.paths, l.path.IsSubpathOf parent ∧
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K)
            l.path.start (requestExit (chosenRequest c.1)) := by
  let T := selectedRequestTrace U S K (chosenRequest c.1)
  let C := selectedErasedCompression U S K (chosenRequest c.1)
  cases hpath : C.path with
  | trivial v =>
      left
      have hi : v = T.initial := by
        have h := C.initial_eq
        rw [hpath] at h
        exact h
      have ht : v = requestExit (chosenRequest c.1) := by
        have h := C.terminal_eq
        rw [hpath] at h
        exact Option.some.inj h
      rw [← hi, ← ht]
  | finite Q =>
      have hback : BackwardLinksOn L.ladder.paths (.finite Q) := by
        simpa only [C, hpath] using
          selectedErasedCompression_backwardLinksOn U S K
            (chosenRequest c.1)
      have hforward : (AltPath.finite Q).directionEdges .forward ⊆
          erasedSelectedSwitchedEdges U S K := by
        intro e he
        apply activeRequest_forwardEdges_subset_switchedEdges U S K c hretained
        simpa only [C, hpath] using he
      rcases Q.initial_or_backwardOwner_reaches_terminal hback hforward with
          hreach | ⟨l, hl, hldir, parent, hparent, hsub, hreach⟩
      · left
        have hi : Q.initial = T.initial := by
          have h := C.initial_eq
          rw [hpath] at h
          exact h
        have ht : Q.terminal = requestExit (chosenRequest c.1) := by
          have h := C.terminal_eq
          rw [hpath] at h
          exact Option.some.inj h
        simpa only [hi, ht] using hreach
      · right
        have ht : Q.terminal = requestExit (chosenRequest c.1) := by
          have h := C.terminal_eq
          rw [hpath] at h
          exact Option.some.inj h
        refine ⟨l, ?_, hldir, parent, hparent, hsub, ?_⟩
        · simpa only [C, hpath] using hl
        · simpa only [ht] using hreach
  | infinite Q =>
      have h := C.terminal_eq
      rw [hpath] at h
      simp at h

end GroundingErasedDecode
end Erdos599
