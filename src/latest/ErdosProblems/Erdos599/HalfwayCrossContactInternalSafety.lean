/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCrossContactForwardRestriction
import ErdosProblems.Erdos599.HalfwayIndexedBackwardSubtraceFlexible

/-!
# Internal safety of an actual cross-contact interval

The cross-contact constructor changes only its two forward boundary links.
Every backward link is unchanged, while every edge lies in the parent.
The parent's concrete indexed backward provenance therefore proves internal
safeness of the interval, including exact per-reference edge intervals.
-/

noncomputable section

open Set

namespace Erdos599.Blueprint

open DirectedPath _root_.Erdos599.Alternating

universe u w

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath} {I : Type w}

theorem crossContactInterval_backwardLink_mem_parent
    (Q : FiniteTrace Gamma.graph) (X : Set V)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first < last)
    (Sfirst : Link.ForwardContactSplit (Q.link first) X)
    (Slast : Link.ForwardContactSplit (Q.link last) X)
    (hlastContact : (Slast.pieceLink Slast.firstPiece).exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X) :
    ∀ l ∈ (AltPath.finite (Q.crossContactInterval X first last hfl Sfirst
      Slast hlastContact hbackwardOff)).links,
      l.direction = .backward → l ∈ (AltPath.finite Q).links := by
  intro l hl hdir
  have hl' := Q.crossContactInterval_links_subset_insert X first last hfl
    Sfirst Slast hlastContact hbackwardOff hl
  rcases hl' with rfl | hl'
  · rw [Slast.pieceLink_direction] at hdir
    contradiction
  · rcases hl' with rfl | hlQ
    · rw [Sfirst.pieceLink_direction] at hdir
      contradiction
    · exact hlQ

/-- Concrete internal safety of the interval, with no child-safety premise. -/
theorem crossContactInterval_internallySafe
    (Q : FiniteTrace Gamma.graph) (X : Set V)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first < last)
    (Sfirst : Link.ForwardContactSplit (Q.link first) X)
    (Slast : Link.ForwardContactSplit (Q.link last) X)
    (hlastContact : (Slast.pieceLink Slast.firstPiece).exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X)
    (hparent : IsSafe Y (.finite Q))
    (P : (AltPath.finite Q).IndexedBackwardProvenance Y I) :
    InternallySafe Y (.finite (Q.crossContactInterval X first last hfl
      Sfirst Slast hlastContact hbackwardOff)) := by
  apply InternallySafe.of_backwardLiteralSubtrace hparent P
  · exact crossContactInterval_backwardLink_mem_parent Q X first last hfl
      Sfirst Slast hlastContact hbackwardOff
  · exact Q.crossContactInterval_edgeSet_subset X first last hfl Sfirst Slast
      hlastContact hbackwardOff

end Erdos599.Blueprint

#print axioms Erdos599.Blueprint.crossContactInterval_backwardLink_mem_parent
#print axioms Erdos599.Blueprint.crossContactInterval_internallySafe
