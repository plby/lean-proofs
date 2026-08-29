/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClassifiedAlternatingIntervalProperties
import ErdosProblems.Erdos599.HalfwayCompressedContactBackwardRestriction

/-!
# Backward provenance of a cross-contact interval

The first and last replacements in a cross-contact interval are forward.
Consequently every backward link is literally an unchanged link of the
parent compressed trace.  This discharges `BackwardLinksRestrictTo`
constructively for the central full-trace segmentation piece.
-/

noncomputable section

open Set

namespace Erdos599

open DirectedPath

namespace Alternating

universe u

variable {V : Type u} {D : Digraph V}

namespace FiniteTrace

theorem replaceLastForwardPrefix_links_subset
    (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hlast : Q.lastLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.lastLink.path))
    (hentry : child.entry = Q.lastLink.entry)
    {X : Set V} (hexitX : child.exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X) :
    (AltPath.finite (Q.replaceLastForwardPrefix child hpositive hlast hchild
      hsub hentry hexitX hbackwardOff)).links ⊆
        insert child (AltPath.finite Q).links := by
  rintro l ⟨i, rfl⟩
  by_cases hi : i.1 = Q.lastIndex
  · simp [replaceLastForwardPrefix, hi]
  · exact Set.mem_insert_iff.mpr (Or.inr ⟨i, by
      simp [replaceLastForwardPrefix, hi]⟩)

end FiniteTrace
end Alternating

namespace Blueprint.LinkageBlueprint

open _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Every backward link of the concrete cross-contact interval is an
unchanged parent link. -/
theorem crossContactInterval_backwardLinksRestrictTo
    (Q : FiniteTrace Gamma.graph) (X : Set V)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first < last)
    (Sfirst : Link.ForwardContactSplit (Q.link first) X)
    (Slast : Link.ForwardContactSplit (Q.link last) X)
    (hlastContact : (Slast.pieceLink Slast.firstPiece).exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X) :
    BackwardLinksRestrictTo
      (.finite (Q.crossContactInterval X first last hfl Sfirst Slast
        hlastContact hbackwardOff)) (.finite Q) := by
  let B := Q.interval first last hfl.le
  have hpositive : 0 < B.lastIndex := by
    dsimp [B]
    omega
  let firstChild := Sfirst.pieceLink Sfirst.lastPiece
  have hBfirst : B.firstLink = Q.link first :=
    FiniteTrace.interval_firstLink Q first last hfl.le
  have hfirstDir : B.firstLink.direction = .forward := by
    rw [hBfirst]
    exact Sfirst.direction_eq
  have hfirstChildDir : firstChild.direction = .forward :=
    Sfirst.pieceLink_direction Sfirst.lastPiece
  have hfirstSub : firstChild.path.IsSubpathOf (.inl B.firstLink.path) := by
    rw [hBfirst]
    exact Sfirst.piece_isSubpathOf Sfirst.lastPiece
  have hfirstExit : firstChild.exit = B.firstLink.exit := by
    rw [hBfirst]
    exact Sfirst.lastPiece_exit
  let F := B.replaceFirstForwardSuffix firstChild hpositive hfirstDir
    hfirstChildDir hfirstSub hfirstExit
  have hFlast : F.lastLink = Q.link last := by
    exact (B.replaceFirstForwardSuffix_lastLink firstChild hpositive hfirstDir
      hfirstChildDir hfirstSub hfirstExit).trans
        (FiniteTrace.interval_lastLink Q first last hfl.le)
  let lastChild := Slast.pieceLink Slast.firstPiece
  have hlastDir : F.lastLink.direction = .forward := by
    rw [hFlast]
    exact Slast.direction_eq
  have hlastChildDir : lastChild.direction = .forward :=
    Slast.pieceLink_direction Slast.firstPiece
  have hlastSub : lastChild.path.IsSubpathOf (.inl F.lastLink.path) := by
    rw [hFlast]
    exact Slast.piece_isSubpathOf Slast.firstPiece
  have hlastEntry : lastChild.entry = F.lastLink.entry := by
    rw [hFlast]
    exact Slast.firstPiece_entry
  have hBoff : ∀ l ∈ (AltPath.finite B).links,
      l.direction = .backward → Disjoint l.path.support X := by
    intro l hl hdir
    exact hbackwardOff l
      (FiniteTrace.interval_links_subset Q first last hfl.le hl) hdir
  have hFoff : ∀ l ∈ (AltPath.finite F).links,
      l.direction = .backward → Disjoint l.path.support X := by
    intro l hl hdir
    have hl' := B.replaceFirstForwardSuffix_links_subset firstChild hpositive
      hfirstDir hfirstChildDir hfirstSub hfirstExit hl
    rcases hl' with rfl | hlB
    · rw [hfirstChildDir] at hdir
      contradiction
    · exact hBoff l hlB hdir
  intro l hl hdir
  have hlF := F.replaceLastForwardPrefix_links_subset lastChild hpositive
    hlastDir hlastChildDir hlastSub hlastEntry hlastContact hFoff hl
  rcases hlF with rfl | hlF
  · rw [hlastChildDir] at hdir
    contradiction
  · have hlB := B.replaceFirstForwardSuffix_links_subset firstChild hpositive
      hfirstDir hfirstChildDir hfirstSub hfirstExit hlF
    rcases hlB with rfl | hlB
    · rw [hfirstChildDir] at hdir
      contradiction
    · have hlQ := FiniteTrace.interval_links_subset Q first last hfl.le hlB
      exact ⟨l, hlQ, hdir, Set.Subset.rfl, Set.Subset.rfl⟩

end Blueprint.LinkageBlueprint
end Erdos599

#print axioms Erdos599.Blueprint.LinkageBlueprint.crossContactInterval_backwardLinksRestrictTo
