/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteForwardContactSplit

/-!
# Literal intervals of an alternating trace

Contact splitting cuts a forward link at a closing-set vertex.  An interval
between contacts on different forward links consists of a suffix of the
first link, all intervening links, and a prefix of the last link.  This file
supplies the missing trace operation.  The compatibility proof is not a
formal restriction argument at the last endpoint: an earlier backward link
could meet the newly exposed end of the prefix.  The actual construction
rules this out because backward links avoid the closing set.
-/

noncomputable section

open Set

namespace Erdos599

open DirectedPath

namespace Alternating

universe u

variable {V : Type u} {D : Digraph V}

namespace Link

/-- Entry preservation when a traversal-compatible sublink still contains
the entry of its parent link. -/
theorem entry_eq_of_subpath_of_parent_entry_mem
    (parent child : Link D)
    (hdir : child.direction = parent.direction)
    (hsub : child.path.IsSubpathOf (.inl parent.path))
    (hmem : parent.entry ∈ child.path.support) :
    child.entry = parent.entry := by
  cases hp : parent.direction with
  | forward =>
      have hc : child.direction = .forward := hdir.trans hp
      simpa [Link.entry, hp, hc] using
        FinitePath.start_eq_of_parent_start_mem
          hsub (by simpa [Link.entry, hp] using hmem)
  | backward =>
      have hc : child.direction = .backward := hdir.trans hp
      simpa [Link.entry, hp, hc] using
        FinitePath.finish_eq_of_parent_finish_mem
          hsub (by simpa [Link.entry, hp] using hmem)

/-- Exit preservation when a traversal-compatible sublink still contains
the exit of its parent link. -/
theorem exit_eq_of_subpath_of_parent_exit_mem
    (parent child : Link D)
    (hdir : child.direction = parent.direction)
    (hsub : child.path.IsSubpathOf (.inl parent.path))
    (hmem : parent.exit ∈ child.path.support) :
    child.exit = parent.exit := by
  cases hp : parent.direction with
  | forward =>
      have hc : child.direction = .forward := hdir.trans hp
      simpa [Link.exit, hp, hc] using
        FinitePath.finish_eq_of_parent_finish_mem
          hsub (by simpa [Link.exit, hp] using hmem)
  | backward =>
      have hc : child.direction = .backward := hdir.trans hp
      simpa [Link.exit, hp, hc] using
        FinitePath.start_eq_of_parent_start_mem
          hsub (by simpa [Link.exit, hp] using hmem)

end Link

/-- Replacing the left forward link of an ordered compatible pair by a
literal suffix preserves compatibility, provided the old traversal exit is
retained. -/
theorem CompatibleInOrder.replace_left_forward_suffix
    {adjacent : Prop} {left right child : Link D}
    (hcompat : CompatibleInOrder adjacent left right)
    (hleft : left.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl left.path))
    (hexit : child.exit = left.exit) :
    CompatibleInOrder adjacent child right := by
  cases hright : right.direction with
  | forward =>
      simp only [CompatibleInOrder, hchild, hright]
      intro x hxchild hxright
      have hxleft : x ∈ left.path.support := hsub.1 hxchild
      have hold := by
        simpa only [CompatibleInOrder, hleft, hright] using hcompat
      rcases hold hxleft hxright with hentry | hexitOld
      · left
        refine ⟨?_, hentry.2⟩
        have hmem : left.entry ∈ child.path.support := hentry.1 ▸ hxchild
        exact hentry.1.trans
          (Link.entry_eq_of_subpath_of_parent_entry_mem left child
            (hchild.trans hleft.symm) hsub hmem).symm
      · right
        exact ⟨hexitOld.1.trans hexit.symm, hexitOld.2⟩
  | backward =>
      have hold := by
        simpa only [CompatibleInOrder, hleft, hright] using hcompat
      simp only [CompatibleInOrder, hchild, hright]
      constructor
      · intro hadj
        have hinter := hold.1 hadj
        apply Set.Subset.antisymm
        · rintro x ⟨hxchild, hxright⟩
          have hxold : x ∈ left.path.support ∩ right.path.support :=
            ⟨hsub.1 hxchild, hxright⟩
          have hx : x = left.exit := by simpa using hinter.subset hxold
          simpa [hx, hexit]
        · rintro x hx
          have hxEq : x = child.exit := by simpa using hx
          subst x
          refine ⟨child.exit_mem_support, ?_⟩
          have holdExit : left.exit ∈ right.path.support :=
            (hinter ▸ Set.mem_singleton left.exit).2
          simpa [hexit] using holdExit
      · intro hnon
        exact (hold.2 hnon).mono hsub.1 Set.Subset.rfl

/-- Replacing the right forward link of an ordered compatible pair by a
literal prefix preserves compatibility.  The only extra case is an earlier
backward link meeting the newly exposed terminal; actual contact splitting
excludes it because that terminal is in `X` and backward links avoid `X`. -/
theorem CompatibleInOrder.replace_right_forward_prefix
    {adjacent : Prop} {left right child : Link D} {X : Set V}
    (hcompat : CompatibleInOrder adjacent left right)
    (hright : right.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl right.path))
    (hentry : child.entry = right.entry)
    (hexitX : child.exit ∈ X)
    (hbackwardOff : left.direction = .backward →
      Disjoint left.path.support X) :
    CompatibleInOrder adjacent left child := by
  cases hleft : left.direction with
  | forward =>
      simp only [CompatibleInOrder, hleft, hchild]
      intro x hxleft hxchild
      have hxright : x ∈ right.path.support := hsub.1 hxchild
      have hold := by
        simpa only [CompatibleInOrder, hleft, hright] using hcompat
      rcases hold hxleft hxright with hentryOld | hexitOld
      · left
        refine ⟨hentryOld.1, ?_⟩
        have hmem : right.exit ∈ child.path.support := hentryOld.2 ▸ hxchild
        exact hentryOld.2.trans
          (Link.exit_eq_of_subpath_of_parent_exit_mem right child
            (hchild.trans hright.symm) hsub hmem).symm
      · right
        exact ⟨hexitOld.1, hexitOld.2.trans hentry.symm⟩
  | backward =>
      have hold := by
        simpa only [CompatibleInOrder, hleft, hright] using hcompat
      simp only [CompatibleInOrder, hleft, hchild]
      constructor
      · intro hadj x hxleft hxchild
        have hxright : x ∈ right.path.support := hsub.1 hxchild
        rcases hold.1 hadj hxleft hxright with hxexit | hxinterior
        · exact Or.inl hxexit
        · right
          refine ⟨hxinterior.1, hxchild, ?_⟩
          intro hxendpoint
          rcases hxendpoint with hxentry | hxexit
          · have hxChildEntry : x = child.entry := by
              simpa [Link.entry, hchild] using hxentry
            have hxRightEntry : x = right.entry := hxChildEntry.trans hentry
            exact hxinterior.2.2 (by
              rw [right.endpoints_eq]
              exact Or.inl hxRightEntry)
          · have hxChildExit : x = child.exit := by
              simpa [Link.exit, hchild] using hxexit
            have hxX : x ∈ X := hxChildExit ▸ hexitX
            exact Set.disjoint_left.1 (hbackwardOff hleft) hxleft hxX
      · intro hnon x hx
        have hxright : x ∈ left.path.support ∩ right.path.support :=
          ⟨hx.1, hsub.1 hx.2⟩
        have hxinterior := hold.2 hnon hxright
        refine ⟨hxinterior.1, hx.2, ?_⟩
        intro hxendpoint
        rcases hxendpoint with hxentry | hxexit
        · have hxChildEntry : x = child.entry := by
            simpa [Link.entry, hchild] using hxentry
          have hxRightEntry : x = right.entry := hxChildEntry.trans hentry
          exact hxinterior.2.2 (by
            rw [right.endpoints_eq]
            exact Or.inl hxRightEntry)
        · have hxChildExit : x = child.exit := by
            simpa [Link.exit, hchild] using hxexit
          have hxX : x ∈ X := hxChildExit ▸ hexitX
          exact Set.disjoint_left.1 (hbackwardOff hleft) hx.1 hxX

namespace FiniteTrace

/-- The literal contiguous interval of a finite alternating trace, before
cutting its first and last forward links. -/
def interval (Q : FiniteTrace D)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first ≤ last) :
    FiniteTrace D where
  lastIndex := last.1 - first.1
  link i := Q.link ⟨first.1 + i.1, by
    have hflv : first.1 ≤ last.1 := hfl
    omega⟩
  joins := by
    intro i
    let j : Fin Q.lastIndex := ⟨first.1 + i.1, by omega⟩
    change (Q.link ⟨first.1 + i.1, _⟩).exit =
      (Q.link ⟨first.1 + (i.1 + 1), _⟩).entry
    have hcast : (⟨first.1 + i.1, by omega⟩ : Fin (Q.lastIndex + 1)) =
        j.castSucc := by
      apply Fin.ext
      simp [j, Nat.add_assoc]
    have hsucc : (⟨first.1 + (i.1 + 1), by omega⟩ :
        Fin (Q.lastIndex + 1)) = j.succ := by
      apply Fin.ext
      simp [j, Nat.add_assoc]
    rw [hcast, hsucc]
    exact Q.joins j
  alternates := by
    intro i
    let j : Fin Q.lastIndex := ⟨first.1 + i.1, by omega⟩
    change (Q.link ⟨first.1 + i.1, _⟩).direction ≠
      (Q.link ⟨first.1 + (i.1 + 1), _⟩).direction
    have hcast : (⟨first.1 + i.1, by omega⟩ : Fin (Q.lastIndex + 1)) =
        j.castSucc := by
      apply Fin.ext
      simp [j]
    have hsucc : (⟨first.1 + (i.1 + 1), by omega⟩ :
        Fin (Q.lastIndex + 1)) = j.succ := by
      apply Fin.ext
      simp [j, Nat.add_assoc]
    rw [hcast, hsucc]
    exact Q.alternates j
  compatible := by
    intro i j hij
    let i' : Fin (Q.lastIndex + 1) := ⟨first.1 + i.1, by omega⟩
    let j' : Fin (Q.lastIndex + 1) := ⟨first.1 + j.1, by omega⟩
    change CompatibleInOrder (j.1 = i.1 + 1) (Q.link i') (Q.link j')
    have hij' : i' < j' := by simpa [i', j'] using hij
    have hadj : (j.1 = i.1 + 1) =
        (j'.1 = i'.1 + 1) := by
      apply propext
      simp only [i', j']
      omega
    rw [hadj]
    exact Q.compatible i' j' hij'

@[simp] theorem interval_lastIndex (Q : FiniteTrace D)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first ≤ last) :
    (Q.interval first last hfl).lastIndex = last.1 - first.1 := rfl

@[simp] theorem interval_link (Q : FiniteTrace D)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first ≤ last)
    (i : Fin (last.1 - first.1 + 1)) :
    (Q.interval first last hfl).link i =
      Q.link ⟨first.1 + i.1, by omega⟩ := rfl

@[simp] theorem interval_firstLink (Q : FiniteTrace D)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first ≤ last) :
    (Q.interval first last hfl).firstLink = Q.link first := by
  apply congrArg Q.link
  apply Fin.ext
  simp [FiniteTrace.firstLink]

@[simp] theorem interval_lastLink (Q : FiniteTrace D)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first ≤ last) :
    (Q.interval first last hfl).lastLink = Q.link last := by
  apply congrArg Q.link
  apply Fin.ext
  simp [FiniteTrace.lastLink]
  omega

theorem interval_links_subset (Q : FiniteTrace D)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first ≤ last) :
    (AltPath.finite (Q.interval first last hfl)).links ⊆
      (AltPath.finite Q).links := by
  rintro l ⟨i, rfl⟩
  have hi : i.1 ≤ last.1 - first.1 := by
    simpa only [interval_lastIndex, Nat.lt_succ_iff] using i.isLt
  exact ⟨⟨first.1 + i.1, by omega⟩, rfl⟩

theorem interval_vertexSet_subset (Q : FiniteTrace D)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first ≤ last) :
    (AltPath.finite (Q.interval first last hfl)).vertexSet ⊆
      (AltPath.finite Q).vertexSet := by
  intro x hx
  simp only [AltPath.vertexSet, FiniteTrace.vertexSet, Set.mem_iUnion] at hx ⊢
  obtain ⟨i, hx⟩ := hx
  have hi : i.1 ≤ last.1 - first.1 := by
    simpa only [interval_lastIndex, Nat.lt_succ_iff] using i.isLt
  exact ⟨⟨first.1 + i.1, by omega⟩, hx⟩

theorem interval_edgeSet_subset (Q : FiniteTrace D)
    (first last : Fin (Q.lastIndex + 1)) (hfl : first ≤ last) :
    (AltPath.finite (Q.interval first last hfl)).edgeSet ⊆
      (AltPath.finite Q).edgeSet := by
  intro e he
  simp only [AltPath.edgeSet, FiniteTrace.edgeSet, Set.mem_iUnion] at he ⊢
  obtain ⟨i, he⟩ := he
  have hi : i.1 ≤ last.1 - first.1 := by
    simpa only [interval_lastIndex, Nat.lt_succ_iff] using i.isLt
  exact ⟨⟨first.1 + i.1, by omega⟩, he⟩

/-- Replace the first forward link by a literal suffix which retains its old
traversal exit.  The trace must have a later link; a one-link contact piece
is represented directly as a singleton trace. -/
def replaceFirstForwardSuffix (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hfirst : Q.firstLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.firstLink.path))
    (hexit : child.exit = Q.firstLink.exit) : FiniteTrace D where
  lastIndex := Q.lastIndex
  link i := if i.1 = 0 then child else Q.link i
  joins := by
    intro i
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hi : i.1 = 0
    · have hcast : i.castSucc =
          (⟨0, Nat.zero_lt_succ Q.lastIndex⟩ : Fin (Q.lastIndex + 1)) :=
        Fin.ext hi
      have hfirstExit : (Q.link i.castSucc).exit = Q.firstLink.exit := by
        rw [hcast]
        rfl
      simpa [hi, hexit, ← hfirstExit] using Q.joins i
    · simpa [hi] using Q.joins i
  alternates := by
    intro i
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hi : i.1 = 0
    · have hcast : i.castSucc =
          (⟨0, Nat.zero_lt_succ Q.lastIndex⟩ : Fin (Q.lastIndex + 1)) :=
        Fin.ext hi
      have hfirstDir : (Q.link i.castSucc).direction = .forward := by
        rw [hcast]
        exact hfirst
      simpa [hi, hchild, ← hfirstDir] using
        Q.alternates i
    · simpa [hi] using Q.alternates i
  compatible := by
    intro i j hij
    have hj : j.1 ≠ 0 := by omega
    by_cases hi : i.1 = 0
    · have hieq : i =
          (⟨0, Nat.zero_lt_succ Q.lastIndex⟩ : Fin (Q.lastIndex + 1)) :=
        Fin.ext hi
      have hleft : (Q.link i).direction = .forward := by
        rw [hieq]
        exact hfirst
      simpa only [hi, if_pos, hj, if_false] using
        (Q.compatible i j hij).replace_left_forward_suffix hleft hchild
          (by simpa only [hieq, FiniteTrace.firstLink] using hsub)
          (by simpa only [hieq, FiniteTrace.firstLink] using hexit)
    · simpa only [hi, if_false, hj] using Q.compatible i j hij

@[simp] theorem replaceFirstForwardSuffix_firstLink
    (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hfirst : Q.firstLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.firstLink.path))
    (hexit : child.exit = Q.firstLink.exit) :
    (Q.replaceFirstForwardSuffix child hpositive hfirst hchild hsub hexit).firstLink =
      child := by
  simp [replaceFirstForwardSuffix, FiniteTrace.firstLink]

theorem replaceFirstForwardSuffix_links_subset
    (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hfirst : Q.firstLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.firstLink.path))
    (hexit : child.exit = Q.firstLink.exit) :
    (AltPath.finite (Q.replaceFirstForwardSuffix child hpositive hfirst hchild
      hsub hexit)).links ⊆ insert child (AltPath.finite Q).links := by
  rintro l ⟨i, rfl⟩
  by_cases hi : i.1 = 0
  · simp [replaceFirstForwardSuffix, hi]
  · exact Set.mem_insert_iff.mpr (Or.inr ⟨i, by
      simp [replaceFirstForwardSuffix, hi]⟩)

/-- Replace the last forward link by a literal prefix ending at a contact in
`X`.  Earlier backward links avoid `X`, which is exactly the nontrivial
compatibility condition at the newly exposed terminal. -/
def replaceLastForwardPrefix (Q : FiniteTrace D) (child : Link D)
    (hpositive : 0 < Q.lastIndex)
    (hlast : Q.lastLink.direction = .forward)
    (hchild : child.direction = .forward)
    (hsub : child.path.IsSubpathOf (.inl Q.lastLink.path))
    (hentry : child.entry = Q.lastLink.entry)
    {X : Set V} (hexitX : child.exit ∈ X)
    (hbackwardOff : ∀ l ∈ (AltPath.finite Q).links,
      l.direction = .backward → Disjoint l.path.support X) : FiniteTrace D where
  lastIndex := Q.lastIndex
  link i := if i.1 = Q.lastIndex then child else Q.link i
  joins := by
    intro i
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hcast : i.1 ≠ Q.lastIndex := by omega
    by_cases hsucc : i.1 + 1 = Q.lastIndex
    · have hlastIndex : i.succ =
          (⟨Q.lastIndex, Nat.lt_succ_self _⟩ : Fin (Q.lastIndex + 1)) := by
        apply Fin.ext
        exact hsucc
      have hlastEntry : (Q.link i.succ).entry = Q.lastLink.entry := by
        rw [hlastIndex]
        rfl
      simpa only [hcast, if_false, hsucc, if_pos, hentry,
        ← hlastEntry] using Q.joins i
    · simpa only [hcast, if_false, hsucc] using Q.joins i
  alternates := by
    intro i
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hcast : i.1 ≠ Q.lastIndex := by omega
    by_cases hsucc : i.1 + 1 = Q.lastIndex
    · have hlastIndex : i.succ =
          (⟨Q.lastIndex, Nat.lt_succ_self _⟩ : Fin (Q.lastIndex + 1)) := by
        apply Fin.ext
        exact hsucc
      have hlastDir : (Q.link i.succ).direction = .forward := by
        rw [hlastIndex]
        exact hlast
      simpa only [hcast, if_false, hsucc, if_pos, hchild,
        ← hlastDir] using Q.alternates i
    · simpa only [hcast, if_false, hsucc] using Q.alternates i
  compatible := by
    intro i j hij
    have hi : i.1 ≠ Q.lastIndex := by omega
    by_cases hj : j.1 = Q.lastIndex
    · have hjeq : j =
          (⟨Q.lastIndex, Nat.lt_succ_self _⟩ : Fin (Q.lastIndex + 1)) :=
        Fin.ext hj
      have hright : (Q.link j).direction = .forward := by
        rw [hjeq]
        exact hlast
      have hsub' : child.path.IsSubpathOf (.inl (Q.link j).path) := by
        simpa only [hjeq, FiniteTrace.lastLink] using hsub
      have hentry' : child.entry = (Q.link j).entry := by
        simpa only [hjeq, FiniteTrace.lastLink] using hentry
      have hoff : (Q.link i).direction = .backward →
          Disjoint (Q.link i).path.support X :=
        hbackwardOff (Q.link i) ⟨i, rfl⟩
      simpa only [hi, if_false, hj, if_pos] using
        (Q.compatible i j hij).replace_right_forward_prefix hright hchild
          hsub' hentry' hexitX hoff
    · simpa only [hi, if_false, hj] using Q.compatible i j hij

@[simp] theorem replaceLastForwardPrefix_lastLink
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
      hexitX hbackwardOff).lastLink = child := by
  simp [replaceLastForwardPrefix, FiniteTrace.lastLink]

end FiniteTrace

end Alternating
end Erdos599

#print axioms Erdos599.Alternating.CompatibleInOrder.replace_left_forward_suffix
#print axioms Erdos599.Alternating.CompatibleInOrder.replace_right_forward_prefix
#print axioms Erdos599.Alternating.FiniteTrace.interval_edgeSet_subset
#print axioms Erdos599.Alternating.FiniteTrace.replaceFirstForwardSuffix
#print axioms Erdos599.Alternating.FiniteTrace.replaceLastForwardPrefix
