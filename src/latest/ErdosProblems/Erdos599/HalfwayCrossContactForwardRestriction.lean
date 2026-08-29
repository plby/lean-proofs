/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCrossContactBackwardRestriction

/-!
# Forward-edge provenance of a cross-contact interval

The two boundary links are literal subpaths of parent forward links and all
intervening links are unchanged.  Hence every retained forward edge is an
actual parent forward edge.
-/

noncomputable section

open Set

namespace Erdos599

open DirectedPath

namespace Alternating

universe u

variable {V : Type u} {D : Digraph V}

namespace FiniteTrace

theorem crossContactInterval_links_subset_insert
    (Q : FiniteTrace D) (X : Set V)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first < last)
    (Sfirst : Link.ForwardContactSplit (Q.link first) X)
    (Slast : Link.ForwardContactSplit (Q.link last) X)
    (hlastContact : (Slast.pieceLink Slast.firstPiece).exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X) :
    (AltPath.finite (Q.crossContactInterval X first last hfl Sfirst Slast
      hlastContact hbackwardOff)).links ⊆
      insert (Slast.pieceLink Slast.firstPiece)
        (insert (Sfirst.pieceLink Sfirst.lastPiece) (AltPath.finite Q).links) := by
  let B := Q.interval first last hfl.le
  have hpositive : 0 < B.lastIndex := by
    dsimp [B]
    omega
  let firstChild := Sfirst.pieceLink Sfirst.lastPiece
  have hBfirst : B.firstLink = Q.link first :=
    interval_firstLink Q first last hfl.le
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
        (interval_lastLink Q first last hfl.le)
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
    exact hbackwardOff l (Q.interval_links_subset first last hfl.le hl) hdir
  have hFoff : ∀ l ∈ (AltPath.finite F).links,
      l.direction = .backward → Disjoint l.path.support X := by
    intro l hl hdir
    have hl' := B.replaceFirstForwardSuffix_links_subset firstChild hpositive
      hfirstDir hfirstChildDir hfirstSub hfirstExit hl
    rcases hl' with rfl | hlB
    · rw [hfirstChildDir] at hdir
      contradiction
    · exact hBoff l hlB hdir
  intro l hl
  have hlF := F.replaceLastForwardPrefix_links_subset lastChild hpositive
    hlastDir hlastChildDir hlastSub hlastEntry hlastContact hFoff hl
  rcases hlF with rfl | hlF
  · exact Set.mem_insert _ _
  · have hlB := B.replaceFirstForwardSuffix_links_subset firstChild hpositive
      hfirstDir hfirstChildDir hfirstSub hfirstExit hlF
    rcases hlB with rfl | hlB
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Q.interval_links_subset first last hfl.le hlB))

theorem crossContactInterval_forwardEdges_subset
    (Q : FiniteTrace D) (X : Set V)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first < last)
    (Sfirst : Link.ForwardContactSplit (Q.link first) X)
    (Slast : Link.ForwardContactSplit (Q.link last) X)
    (hlastContact : (Slast.pieceLink Slast.firstPiece).exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X) :
    (AltPath.finite (Q.crossContactInterval X first last hfl Sfirst Slast
      hlastContact hbackwardOff)).directionEdges .forward ⊆
        (AltPath.finite Q).directionEdges .forward := by
  intro e he
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨l, hl, hldir, hel⟩ := he
  have hl' := Q.crossContactInterval_links_subset_insert X first last hfl
    Sfirst Slast hlastContact hbackwardOff hl
  rcases hl' with rfl | hl'
  · exact ⟨Q.link last, ⟨last, rfl⟩, Slast.direction_eq,
      Slast.piece_edgeSet_subset Slast.firstPiece hel⟩
  · rcases hl' with rfl | hlQ
    · exact ⟨Q.link first, ⟨first, rfl⟩, Sfirst.direction_eq,
        Sfirst.piece_edgeSet_subset Sfirst.lastPiece hel⟩
    · exact ⟨l, hlQ, hldir, hel⟩

end FiniteTrace
end Alternating
end Erdos599

#print axioms Erdos599.Alternating.FiniteTrace.crossContactInterval_links_subset_insert
#print axioms Erdos599.Alternating.FiniteTrace.crossContactInterval_forwardEdges_subset
