/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayAlternatingIntervalCore
import ErdosProblems.Erdos599.ArbitraryReferenceEndpointClassification

/-!
# Contact intervals across distinct forward links

This file assembles the final piece of the first cut into the first piece of
a later cut.  It is the concrete cross-link case of full contact
segmentation.  The intervening alternating links are retained literally.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

namespace Link.ForwardContactSplit

variable {l : Link D} {X : Set V}

/-- The last literal piece in the ordered split. -/
noncomputable def lastPiece (S : Link.ForwardContactSplit l X) : S.Piece :=
  ⟨S.split.pieces.getLast S.split.pieces_ne,
    List.getLast_mem S.split.pieces_ne⟩

/-- The first literal piece in the ordered split. -/
noncomputable def firstPiece (S : Link.ForwardContactSplit l X) : S.Piece :=
  ⟨S.split.pieces.head S.split.pieces_ne,
    List.head_mem S.split.pieces_ne⟩

@[simp] theorem lastPiece_exit (S : Link.ForwardContactSplit l X) :
    (S.pieceLink S.lastPiece).exit = l.exit := by
  change (S.split.pieces.getLast S.split.pieces_ne).finish = l.exit
  rw [S.split.last_finish]
  simp [Link.exit, S.direction_eq]

@[simp] theorem firstPiece_entry (S : Link.ForwardContactSplit l X) :
    (S.pieceLink S.firstPiece).entry = l.entry := by
  change (S.split.pieces.head S.split.pieces_ne).start = l.entry
  rw [S.split.first_start]
  simp [Link.entry, S.direction_eq]

end Link.ForwardContactSplit

namespace FiniteTrace

theorem replaceFirstForwardSuffix_lastLink
    (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hfirst : Q.firstLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.firstLink.path))
    (hexit : child.exit = Q.firstLink.exit) :
    (Q.replaceFirstForwardSuffix child hpositive hfirst hchild hsub hexit).lastLink =
      Q.lastLink := by
  simp only [FiniteTrace.lastLink, replaceFirstForwardSuffix]
  rw [if_neg (by omega)]

theorem replaceFirstForwardSuffix_vertexSet_subset
    (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hfirst : Q.firstLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.firstLink.path))
    (hexit : child.exit = Q.firstLink.exit) :
    (AltPath.finite (Q.replaceFirstForwardSuffix child hpositive hfirst hchild
      hsub hexit)).vertexSet ⊆ (AltPath.finite Q).vertexSet := by
  intro x hx
  simp only [AltPath.vertexSet, FiniteTrace.vertexSet, Set.mem_iUnion] at hx ⊢
  obtain ⟨i, hx⟩ := hx
  by_cases hi : i.1 = 0
  · have hxchild : x ∈ child.path.support := by
      simpa [replaceFirstForwardSuffix, hi] using hx
    have hxfirst : x ∈ Q.firstLink.path.support := hsub.1 hxchild
    exact ⟨⟨0, Nat.zero_lt_succ _⟩, hxfirst⟩
  · exact ⟨i, by simpa [replaceFirstForwardSuffix, hi] using hx⟩

theorem replaceFirstForwardSuffix_edgeSet_subset
    (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hfirst : Q.firstLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.firstLink.path))
    (hexit : child.exit = Q.firstLink.exit) :
    (AltPath.finite (Q.replaceFirstForwardSuffix child hpositive hfirst hchild
      hsub hexit)).edgeSet ⊆ (AltPath.finite Q).edgeSet := by
  intro e he
  simp only [AltPath.edgeSet, FiniteTrace.edgeSet, Set.mem_iUnion] at he ⊢
  obtain ⟨i, he⟩ := he
  by_cases hi : i.1 = 0
  · have hechild : e ∈ child.path.edgeSet := by
      simpa [replaceFirstForwardSuffix, hi] using he
    have hefirst : e ∈ Q.firstLink.path.edgeSet := hsub.2 hechild
    exact ⟨⟨0, Nat.zero_lt_succ _⟩, hefirst⟩
  · exact ⟨i, by simpa [replaceFirstForwardSuffix, hi] using he⟩

theorem replaceLastForwardPrefix_vertexSet_subset
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
      hsub hentry hexitX hbackwardOff)).vertexSet ⊆
      (AltPath.finite Q).vertexSet := by
  intro x hx
  simp only [AltPath.vertexSet, FiniteTrace.vertexSet, Set.mem_iUnion] at hx ⊢
  obtain ⟨i, hx⟩ := hx
  by_cases hi : i.1 = Q.lastIndex
  · have hxchild : x ∈ child.path.support := by
      simpa [replaceLastForwardPrefix, hi] using hx
    have hxlast : x ∈ Q.lastLink.path.support := hsub.1 hxchild
    exact ⟨⟨Q.lastIndex, Nat.lt_succ_self _⟩, hxlast⟩
  · exact ⟨i, by simpa [replaceLastForwardPrefix, hi] using hx⟩

theorem replaceLastForwardPrefix_edgeSet_subset
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
      hsub hentry hexitX hbackwardOff)).edgeSet ⊆
      (AltPath.finite Q).edgeSet := by
  intro e he
  simp only [AltPath.edgeSet, FiniteTrace.edgeSet, Set.mem_iUnion] at he ⊢
  obtain ⟨i, he⟩ := he
  by_cases hi : i.1 = Q.lastIndex
  · have hechild : e ∈ child.path.edgeSet := by
      simpa [replaceLastForwardPrefix, hi] using he
    have helast : e ∈ Q.lastLink.path.edgeSet := hsub.2 hechild
    exact ⟨⟨Q.lastIndex, Nat.lt_succ_self _⟩, helast⟩
  · exact ⟨i, by simpa [replaceLastForwardPrefix, hi] using he⟩

/-- The concrete finite alternating interval between the last contact piece
of one forward link and the first contact piece of a later forward link. -/
noncomputable def crossContactInterval
    (Q : FiniteTrace D) (X : Set V)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first < last)
    (Sfirst : Link.ForwardContactSplit (Q.link first) X)
    (Slast : Link.ForwardContactSplit (Q.link last) X)
    (hlastContact : (Slast.pieceLink Slast.firstPiece).exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X) : FiniteTrace D := by
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
  exact F.replaceLastForwardPrefix lastChild hpositive hlastDir
    hlastChildDir hlastSub hlastEntry hlastContact hFoff

end FiniteTrace
end Alternating
end Erdos599

#print axioms Erdos599.Alternating.FiniteTrace.crossContactInterval
#print axioms Erdos599.Alternating.FiniteTrace.replaceFirstForwardSuffix_edgeSet_subset
#print axioms Erdos599.Alternating.FiniteTrace.replaceLastForwardPrefix_edgeSet_subset
