/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClassifiedAlternatingInterval

/-!
# Exact boundary and restriction laws for cross-contact intervals

The concrete cross-link interval begins at the last contact piece in its
first forward run and ends at the first contact piece in its last forward
run.  This file records those exact endpoints and the literal restriction
to the parent compressed trace.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

namespace FiniteTrace

@[simp] theorem replaceLastForwardPrefix_firstLink
    (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hlast : Q.lastLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.lastLink.path))
    (hentry : child.entry = Q.lastLink.entry)
    {X : Set V} (hexitX : child.exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X) :
    (Q.replaceLastForwardPrefix child hpositive hlast hchild hsub hentry
      hexitX hbackwardOff).firstLink = Q.firstLink := by
  change (if (0 : Nat) = Q.lastIndex then child else
      Q.link ⟨0, Nat.zero_lt_succ _⟩) = Q.firstLink
  rw [if_neg (by omega)]
  rfl

@[simp] theorem replaceFirstForwardSuffix_initial
    (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hfirst : Q.firstLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.firstLink.path))
    (hexit : child.exit = Q.firstLink.exit) :
    (Q.replaceFirstForwardSuffix child hpositive hfirst hchild hsub
      hexit).initial = child.entry := by
  rw [FiniteTrace.initial, replaceFirstForwardSuffix_firstLink]

@[simp] theorem replaceLastForwardPrefix_initial
    (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hlast : Q.lastLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.lastLink.path))
    (hentry : child.entry = Q.lastLink.entry)
    {X : Set V} (hexitX : child.exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X) :
    (Q.replaceLastForwardPrefix child hpositive hlast hchild hsub hentry
      hexitX hbackwardOff).initial = Q.initial := by
  rw [FiniteTrace.initial, replaceLastForwardPrefix_firstLink]
  rfl

@[simp] theorem replaceLastForwardPrefix_terminal
    (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hlast : Q.lastLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.lastLink.path))
    (hentry : child.entry = Q.lastLink.entry)
    {X : Set V} (hexitX : child.exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X) :
    (Q.replaceLastForwardPrefix child hpositive hlast hchild hsub hentry
      hexitX hbackwardOff).terminal = child.exit := by
  rw [FiniteTrace.terminal, replaceLastForwardPrefix_lastLink]

variable (Q : FiniteTrace D) (X : Set V)
variable (first last : Fin (Q.lastIndex + 1)) (hfl : first < last)
variable (Sfirst : Link.ForwardContactSplit (Q.link first) X)
variable (Slast : Link.ForwardContactSplit (Q.link last) X)
variable (hlastContact : (Slast.pieceLink Slast.firstPiece).exit ∈ X)
variable (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
  l.direction = .backward → Disjoint l.path.support X)

@[simp] theorem crossContactInterval_initial :
    (Q.crossContactInterval X first last hfl Sfirst Slast hlastContact
      hbackwardOff).initial =
        (Sfirst.pieceLink Sfirst.lastPiece).entry := by
  have hpos : 0 < last.1 - first.1 := Nat.sub_pos_of_lt hfl
  simp only [crossContactInterval]
  simp [FiniteTrace.initial, FiniteTrace.firstLink,
    replaceLastForwardPrefix, replaceFirstForwardSuffix]
  rw [if_neg (Nat.ne_of_lt hpos)]
  rfl

@[simp] theorem crossContactInterval_terminal :
    (Q.crossContactInterval X first last hfl Sfirst Slast hlastContact
      hbackwardOff).terminal =
        (Slast.pieceLink Slast.firstPiece).exit := by
  simp only [crossContactInterval]
  simp [FiniteTrace.terminal, FiniteTrace.lastLink,
    replaceLastForwardPrefix]

theorem crossContactInterval_vertexSet_subset :
    (AltPath.finite (Q.crossContactInterval X first last hfl Sfirst Slast
      hlastContact hbackwardOff)).vertexSet ⊆
        (AltPath.finite Q).vertexSet := by
  simp only [crossContactInterval]
  let B := Q.interval first last hfl.le
  let firstChild := Sfirst.pieceLink Sfirst.lastPiece
  have hpositive : 0 < B.lastIndex := by
    dsimp [B]
    omega
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
  exact (F.replaceLastForwardPrefix_vertexSet_subset lastChild hpositive
      hlastDir hlastChildDir hlastSub hlastEntry hlastContact hFoff).trans
    ((B.replaceFirstForwardSuffix_vertexSet_subset firstChild hpositive
      hfirstDir hfirstChildDir hfirstSub hfirstExit).trans
      (Q.interval_vertexSet_subset first last hfl.le))

theorem crossContactInterval_edgeSet_subset :
    (AltPath.finite (Q.crossContactInterval X first last hfl Sfirst Slast
      hlastContact hbackwardOff)).edgeSet ⊆
        (AltPath.finite Q).edgeSet := by
  simp only [crossContactInterval]
  let B := Q.interval first last hfl.le
  let firstChild := Sfirst.pieceLink Sfirst.lastPiece
  have hpositive : 0 < B.lastIndex := by
    dsimp [B]
    omega
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
  exact (F.replaceLastForwardPrefix_edgeSet_subset lastChild hpositive
      hlastDir hlastChildDir hlastSub hlastEntry hlastContact hFoff).trans
    ((B.replaceFirstForwardSuffix_edgeSet_subset firstChild hpositive
      hfirstDir hfirstChildDir hfirstSub hfirstExit).trans
      (Q.interval_edgeSet_subset first last hfl.le))

end FiniteTrace
end Alternating
end Erdos599

#print axioms Erdos599.Alternating.FiniteTrace.crossContactInterval_initial
#print axioms Erdos599.Alternating.FiniteTrace.crossContactInterval_terminal
#print axioms Erdos599.Alternating.FiniteTrace.crossContactInterval_vertexSet_subset
#print axioms Erdos599.Alternating.FiniteTrace.crossContactInterval_edgeSet_subset
