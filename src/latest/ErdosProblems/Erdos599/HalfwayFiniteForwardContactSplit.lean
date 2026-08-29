/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingTraceOps
import ErdosProblems.Erdos599.SliceSuffixFromAux
import ErdosProblems.Erdos599.BlueprintSplice

/-!
# Splitting a finite forward path at every contact with a closed set

A projected forward link need not be contained in one literal fractured
piece: recombination can make it pass through several cut vertices.  This
file performs the required second cut.  It is purely finite path geometry
and makes no closure assumption on the ambient warp.

The pieces occur in their original order, concatenate to the original
support word, preserve every directed edge, and meet the cutting set only
at their two displayed endpoints.  In particular each piece retains a
literal `IsSubpathOf` certificate in the original forward link.
-/

noncomputable section

open Set

namespace Erdos599
namespace DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

namespace FinitePath

/-- Concatenate path-support words while deleting the repeated initial
vertex of every piece after the first. -/
def joinSupports (pieces : List (FinitePath D)) : List V :=
  match pieces with
  | [] => []
  | p :: ps => p.walk.support ++
      (ps.map (fun q => q.walk.support.tail)).flatten

@[simp] theorem joinSupports_nil :
    joinSupports ([] : List (FinitePath D)) = [] := rfl

@[simp] theorem joinSupports_singleton (p : FinitePath D) :
    joinSupports [p] = p.walk.support := by
  simp [joinSupports]

private theorem joinSupports_append (left right : List (FinitePath D))
    (hleft : left ≠ []) :
    joinSupports (left ++ right) =
      joinSupports left ++
        (right.map (fun q => q.walk.support.tail)).flatten := by
  cases left with
  | nil => exact (hleft rfl).elim
  | cons p ps =>
      simp only [joinSupports, List.cons_append, List.map_append,
        List.flatten_append]
      simp only [List.append_assoc]

private theorem flatten_tails_eq_tail_joinSupports
    (pieces : List (FinitePath D)) (hne : pieces ≠ []) :
    (pieces.map (fun q => q.walk.support.tail)).flatten =
      (joinSupports pieces).tail := by
  cases pieces with
  | nil => exact (hne rfl).elim
  | cons p ps =>
      simp only [joinSupports, List.map_cons, List.flatten_cons]
      rw [List.tail_append_of_ne_nil p.walk.support_ne_nil]

/-- A concrete decomposition of a nontrivial finite directed path at all
contacts with `X`.  `support_word_exact` is the literal ordered
concatenation statement, while the two union equalities are convenient for
the alternating-path consumers. -/
structure ContactSplit (p : FinitePath D) (X : Set V) where
  pieces : List (FinitePath D)
  pieces_ne : pieces ≠ []
  chain : pieces.IsChain (fun q r => q.finish = r.start)
  first_start : (pieces.head pieces_ne).start = p.start
  last_finish : (pieces.getLast pieces_ne).finish = p.finish
  endpoint_only : ∀ q ∈ pieces,
    q.support ∩ X ⊆ {q.start, q.finish}
  nontrivial : ∀ q ∈ pieces, q.start ≠ q.finish
  start_contact : ∀ q ∈ pieces, q.start = p.start ∨ q.start ∈ X
  finish_contact : ∀ q ∈ pieces, q.finish = p.finish ∨ q.finish ∈ X
  subpath : ∀ q ∈ pieces, q.IsSubpathOf (.inl p)
  support_word_exact : joinSupports pieces = p.walk.support
  vertexSet_exact : (⋃ q ∈ pieces, q.support) = p.support
  edgeSet_exact : (⋃ q ∈ pieces, q.edgeSet) = p.edgeSet

namespace ContactSplit

variable {p q : FinitePath D} {X : Set V}

/-- The one-piece split, used exactly when the original path has no
internal `X`-contact. -/
def singleton (p : FinitePath D) (X : Set V) (hne : p.start ≠ p.finish)
    (hclean : p.support ∩ X ⊆ {p.start, p.finish}) : ContactSplit p X where
  pieces := [p]
  pieces_ne := by simp
  chain := by simp
  first_start := rfl
  last_finish := rfl
  endpoint_only := by
    intro q hq
    have hqp : q = p := List.mem_singleton.mp hq
    subst q
    exact hclean
  nontrivial := by
    intro q hq
    have hqp : q = p := List.mem_singleton.mp hq
    simpa only [hqp] using hne
  start_contact := by
    intro q hq
    exact Or.inl (by simpa using congrArg FinitePath.start (List.mem_singleton.mp hq))
  finish_contact := by
    intro q hq
    exact Or.inl (by simpa using congrArg FinitePath.finish (List.mem_singleton.mp hq))
  subpath := by
    intro q hq
    simpa [List.mem_singleton.mp hq] using p.isSubpathOf_self
  support_word_exact := by simp
  vertexSet_exact := by simp
  edgeSet_exact := by simp

/-- Append two already split paths at an `X`-contact.  This is the exact
inductive splice used by `exists_contactSplit`; it is also useful when a
caller has already selected a distinguished contact. -/
def append (A : ContactSplit p X) (B : ContactSplit q X)
    (hstart : q.start = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish})
    (hcontact : p.finish ∈ X) :
    ContactSplit (p.appendFinite q hstart hinter) X where
  pieces := A.pieces ++ B.pieces
  pieces_ne := by simp [A.pieces_ne]
  chain := by
    apply A.chain.append B.chain
    intro a ha b hb
    rw [List.getLast?_eq_some_getLast A.pieces_ne] at ha
    rw [List.head?_eq_some_head B.pieces_ne] at hb
    have ha' : a = A.pieces.getLast A.pieces_ne := Option.some.inj ha.symm
    have hb' : b = B.pieces.head B.pieces_ne := Option.some.inj hb.symm
    subst a
    subst b
    exact A.last_finish.trans (hstart ▸ B.first_start.symm)
  first_start := by
    rw [List.head_append_of_ne_nil A.pieces_ne]
    exact A.first_start.trans (p.appendFinite_start q hstart hinter).symm
  last_finish := by
    rw [List.getLast_append_right B.pieces_ne]
    exact B.last_finish.trans (p.appendFinite_finish q hstart hinter).symm
  endpoint_only := by
    intro r hr
    rw [List.mem_append] at hr
    exact hr.elim (A.endpoint_only r) (B.endpoint_only r)
  nontrivial := by
    intro r hr
    rw [List.mem_append] at hr
    exact hr.elim (A.nontrivial r) (B.nontrivial r)
  start_contact := by
    intro r hr
    rw [List.mem_append] at hr
    rcases hr with hr | hr
    · rcases A.start_contact r hr with hrstart | hrX
      · exact Or.inl (hrstart.trans (p.appendFinite_start q hstart hinter).symm)
      · exact Or.inr hrX
    · rcases B.start_contact r hr with hrstart | hrX
      · exact Or.inr (hrstart ▸ hstart ▸ hcontact)
      · exact Or.inr hrX
  finish_contact := by
    intro r hr
    rw [List.mem_append] at hr
    rcases hr with hr | hr
    · rcases A.finish_contact r hr with hrfinish | hrX
      · exact Or.inr (hrfinish ▸ hcontact)
      · exact Or.inr hrX
    · rcases B.finish_contact r hr with hrfinish | hrX
      · exact Or.inl (hrfinish.trans (p.appendFinite_finish q hstart hinter).symm)
      · exact Or.inr hrX
  subpath := by
    intro r hr
    rw [List.mem_append] at hr
    change r.support ⊆ (p.appendFinite q hstart hinter).support ∧
      r.edgeSet ⊆ (p.appendFinite q hstart hinter).edgeSet
    rw [FinitePath.support_appendFinite_eq_union]
    rw [Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite]
    rcases hr with hr | hr
    · exact ⟨(A.subpath r hr).1.trans Set.subset_union_left,
        (A.subpath r hr).2.trans Set.subset_union_left⟩
    · exact ⟨(B.subpath r hr).1.trans Set.subset_union_right,
        (B.subpath r hr).2.trans Set.subset_union_right⟩
  support_word_exact := by
    rw [joinSupports_append A.pieces B.pieces A.pieces_ne,
      flatten_tails_eq_tail_joinSupports B.pieces B.pieces_ne,
      A.support_word_exact, B.support_word_exact,
      p.appendFinite_walk_support q hstart hinter]
  vertexSet_exact := by
    rw [FinitePath.support_appendFinite_eq_union]
    calc
      (⋃ r ∈ A.pieces ++ B.pieces, r.support) =
          (⋃ r ∈ A.pieces, r.support) ∪ ⋃ r ∈ B.pieces, r.support := by
        ext x
        simp only [List.mem_append, Set.mem_iUnion, Set.mem_union]
        aesop
      _ = p.support ∪ q.support := by rw [A.vertexSet_exact, B.vertexSet_exact]
  edgeSet_exact := by
    rw [Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite]
    calc
      (⋃ r ∈ A.pieces ++ B.pieces, r.edgeSet) =
          (⋃ r ∈ A.pieces, r.edgeSet) ∪ ⋃ r ∈ B.pieces, r.edgeSet := by
        ext e
        simp only [List.mem_append, Set.mem_iUnion, Set.mem_union]
        aesop
      _ = p.edgeSet ∪ q.edgeSet := by rw [A.edgeSet_exact, B.edgeSet_exact]

theorem every_contact_is_piece_endpoint (A : ContactSplit p X) :
    p.support ∩ X ⊆
      {x | ∃ q ∈ A.pieces, x = q.start ∨ x = q.finish} := by
  intro x hx
  rw [← A.vertexSet_exact] at hx
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx.1
  obtain ⟨hqmem, hxq⟩ := Set.mem_iUnion.mp hq
  have hend := A.endpoint_only q hqmem ⟨hxq, hx.2⟩
  exact ⟨q, hqmem, by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hend⟩

theorem piece_subpath_of_owner (A : ContactSplit p X)
    {owner : Path D} (hp : p.IsSubpathOf owner)
    {q : FinitePath D} (hq : q ∈ A.pieces) : q.IsSubpathOf owner :=
  ⟨(A.subpath q hq).1.trans hp.1, (A.subpath q hq).2.trans hp.2⟩

end ContactSplit

/-- A directed subpath which contains the initial vertex of its finite
parent must itself begin there. -/
theorem start_eq_of_parent_start_mem {p q : FinitePath D}
    (hsub : q.IsSubpathOf (.inl p))
    (hstart : p.start ∈ q.support) : q.start = p.start := by
  let hmeet : p.walk.Meets ({q.start} : Set V) :=
    ⟨q.start, hsub.1 q.start_mem_support, Set.mem_singleton q.start⟩
  let front := p.firstHit {q.start} hmeet
  have hfrontFinish : front.finish = q.start := by
    have h := p.firstHit_finish_mem {q.start} hmeet
    simpa only [Set.mem_singleton_iff] using h
  have hfrontSub : front.IsSubpathOf (.inl p) :=
    p.firstHit_isSubpathOf {q.start} hmeet
  have hinter := support_inter_subset_singleton_of_isSubpathOf
    front q (.inl p) hfrontSub hsub hfrontFinish
  have hpfront : p.start ∈ front.support := by
    change front.start ∈ front.support
    exact front.start_mem_support
  have hp : p.start = front.finish := by
    simpa only [Set.mem_singleton_iff] using hinter ⟨hpfront, hstart⟩
  exact hfrontFinish.symm.trans hp.symm

/-- A directed subpath which contains the terminal vertex of its finite
parent must itself end there. -/
theorem finish_eq_of_parent_finish_mem {p q : FinitePath D}
    (hsub : q.IsSubpathOf (.inl p))
    (hfinish : p.finish ∈ q.support) : q.finish = p.finish := by
  let hqfinish : q.finish ∈ p.support := hsub.1 q.finish_mem_support
  let tail := p.suffixFromAux q.finish hqfinish
  have htailStart : tail.start = q.finish :=
    p.suffixFromAux_start q.finish hqfinish
  have htailSub : tail.IsSubpathOf (.inl p) :=
    CardinalInduction.SliceCandidate.suffixFromAux_isSubpathOf_stage
      p q.finish hqfinish
  have hinter := support_inter_subset_singleton_of_isSubpathOf
    q tail (.inl p) hsub htailSub htailStart.symm
  have hptail : p.finish ∈ tail.support := by
    change tail.finish ∈ tail.support
    exact tail.finish_mem_support
  have hp : p.finish = q.finish := by
    simpa only [Set.mem_singleton_iff] using hinter ⟨hfinish, hptail⟩
  exact hp.symm

private theorem firstHit_prefix (p : FinitePath D) (S : Set V)
    (hS : p.walk.Meets S) : (p.firstHit S hS).IsPrefixOf p :=
  (p.walk.firstHit S hS).support_prefix

private theorem prefix_length_lt_of_finish_ne
    {a b : FinitePath D} (hab : a.IsPrefixOf b)
    (hne : a.finish ≠ b.finish) :
    a.walk.support.length < b.walk.support.length := by
  apply Nat.lt_of_le_of_ne hab.length_le
  intro hlen
  have heq := hab.eq_of_length hlen
  apply hne
  have hlast := congrArg List.getLast? heq
  rw [List.getLast?_eq_some_getLast a.walk.support_ne_nil,
    List.getLast?_eq_some_getLast b.walk.support_ne_nil,
    a.walk.getLast_support, b.walk.getLast_support] at hlast
  exact Option.some.inj hlast

private theorem suffix_length_lt_of_start_ne
    (p : FinitePath D) (x : V) (hx : x ∈ p.support)
    (hne : x ≠ p.start) :
    (p.suffixFromAux x hx).walk.support.length < p.walk.support.length := by
  have hsuffix : (p.suffixFromAux x hx).walk.support <:+ p.walk.support :=
    p.suffixData_support_suffix x hx
  apply Nat.lt_of_le_of_ne hsuffix.length_le
  intro hlen
  have heq := hsuffix.eq_of_length hlen
  apply hne
  have hhead := congrArg List.head? heq
  rw [List.head?_eq_some_head (p.suffixFromAux x hx).walk.support_ne_nil,
    List.head?_eq_some_head p.walk.support_ne_nil,
    (p.suffixFromAux x hx).walk.head_support, p.walk.head_support] at hhead
  exact (p.suffixFromAux_start x hx).symm.trans (Option.some.inj hhead)

/-- Every nontrivial finite directed path admits the concrete all-contact
split.  No ambient warp closure, source containment, or target containment
is used. -/
theorem exists_contactSplit (p : FinitePath D) (X : Set V)
    (hne : p.start ≠ p.finish) : Nonempty (ContactSplit p X) := by
  classical
  have aux : ∀ n : ℕ, ∀ p : FinitePath D,
      p.walk.support.length = n → p.start ≠ p.finish →
        Nonempty (ContactSplit p X) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro p hlen hpne
        by_cases hclean : p.support ∩ X ⊆ {p.start, p.finish}
        · exact ⟨ContactSplit.singleton p X hpne hclean⟩
        · obtain ⟨x, hxpX, hxends⟩ := Set.not_subset.mp hclean
          have hxp : x ∈ p.support := hxpX.1
          have hxX : x ∈ X := hxpX.2
          have hxstart : x ≠ p.start := by
            intro hx
            apply hxends
            simp [hx]
          have hxfinish : x ≠ p.finish := by
            intro hx
            apply hxends
            simp [hx]
          let hmeet : p.walk.Meets ({x} : Set V) :=
            ⟨x, hxp, Set.mem_singleton x⟩
          let front : FinitePath D := p.firstHit {x} hmeet
          have hfrontFinish : front.finish = x := by
            have h := p.firstHit_finish_mem {x} hmeet
            simpa only [Set.mem_singleton_iff] using h
          have hfrontPrefix : front.IsPrefixOf p := firstHit_prefix p {x} hmeet
          have hfrontLen : front.walk.support.length < n := by
            rw [← hlen]
            exact prefix_length_lt_of_finish_ne hfrontPrefix
              (hfrontFinish.trans_ne hxfinish)
          have hfrontNe : front.start ≠ front.finish := by
            change p.start ≠ front.finish
            simpa only [hfrontFinish] using Ne.symm hxstart
          let hxfront : front.finish ∈ p.support :=
            hfrontPrefix.support_subset front.finish_mem_support
          let tail : FinitePath D := p.suffixFromAux front.finish hxfront
          have htailStart : tail.start = front.finish :=
            p.suffixFromAux_start front.finish hxfront
          have htailFinish : tail.finish = p.finish :=
            p.suffixFromAux_finish front.finish hxfront
          have htailLen : tail.walk.support.length < n := by
            rw [← hlen]
            apply suffix_length_lt_of_start_ne p front.finish hxfront
            exact hfrontFinish.trans_ne hxstart
          have htailNe : tail.start ≠ tail.finish := by
            rw [htailStart, htailFinish, hfrontFinish]
            exact hxfinish
          obtain ⟨A⟩ := ih front.walk.support.length hfrontLen front rfl hfrontNe
          obtain ⟨B⟩ := ih tail.walk.support.length htailLen tail rfl htailNe
          obtain ⟨hstart, hinter, _hinterEq, happend⟩ :=
            CardinalInduction.SliceCandidate.appendFinite_suffixFromAux_eq_of_prefix
              hfrontPrefix
          have hinter' : front.support ∩ tail.support ⊆ {front.finish} := by
            simpa only [tail] using hinter
          have happend' : front.appendFinite tail htailStart hinter' = p := by
            simpa only [tail] using happend
          have C := ContactSplit.append A B htailStart hinter'
            (hfrontFinish ▸ hxX)
          exact ⟨happend' ▸ C⟩
  exact aux p.walk.support.length p rfl hne

end FinitePath
end DirectedPath

namespace Alternating
namespace Link

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

/-- The concrete all-contact split of one forward alternating link.  The
underlying ordered list is retained verbatim so a trace-level compiler can
replace this link by its children without losing link order. -/
structure ForwardContactSplit (l : Link D) (X : Set V) where
  direction_eq : l.direction = .forward
  split : FinitePath.ContactSplit l.path X

namespace ForwardContactSplit

variable {l : Link D} {X : Set V}

/-- A child path, bundled with its literal occurrence in the ordered split. -/
abbrev Piece (S : ForwardContactSplit l X) :=
  {q : FinitePath D // q ∈ S.split.pieces}

/-- Every child is again a genuine forward link. -/
def pieceLink (S : ForwardContactSplit l X) (q : S.Piece) : Link D where
  path := q.1
  direction := .forward
  nontrivial := S.split.nontrivial q.1 q.2

@[simp] theorem pieceLink_path (S : ForwardContactSplit l X) (q : S.Piece) :
    (S.pieceLink q).path = q.1 := rfl

@[simp] theorem pieceLink_direction
    (S : ForwardContactSplit l X) (q : S.Piece) :
    (S.pieceLink q).direction = .forward := rfl

@[simp] theorem pieceLink_entry (S : ForwardContactSplit l X) (q : S.Piece) :
    (S.pieceLink q).entry = q.1.start := rfl

@[simp] theorem pieceLink_exit (S : ForwardContactSplit l X) (q : S.Piece) :
    (S.pieceLink q).exit = q.1.finish := rfl

theorem piece_endpoint_only (S : ForwardContactSplit l X) (q : S.Piece) :
    q.1.support ∩ X ⊆ {q.1.start, q.1.finish} :=
  S.split.endpoint_only q.1 q.2

theorem piece_isSubpathOf (S : ForwardContactSplit l X) (q : S.Piece) :
    q.1.IsSubpathOf (.inl l.path) :=
  S.split.subpath q.1 q.2

theorem piece_edgeSet_subset (S : ForwardContactSplit l X) (q : S.Piece) :
    q.1.edgeSet ⊆ l.path.edgeSet :=
  (S.piece_isSubpathOf q).2

theorem piece_isSubpathOf_owner (S : ForwardContactSplit l X)
    (q : S.Piece) {owner : Path D} (hl : l.path.IsSubpathOf owner) :
    q.1.IsSubpathOf owner :=
  S.split.piece_subpath_of_owner hl q.2

/-- If the original traversal entry occurs in a child, it is the child's
entry.  This is the endpoint fact needed to inherit cross-link
`CompatibleInOrder` certificates after splitting. -/
theorem piece_entry_eq_of_parent_entry_mem
    (S : ForwardContactSplit l X) (q : S.Piece)
    (hmem : l.entry ∈ q.1.support) : (S.pieceLink q).entry = l.entry := by
  have hstart : l.path.start ∈ q.1.support := by
    simpa only [Link.entry, S.direction_eq] using hmem
  have h := FinitePath.start_eq_of_parent_start_mem (S.piece_isSubpathOf q) hstart
  change q.1.start = l.entry
  rw [show l.entry = l.path.start by simp only [Link.entry, S.direction_eq]]
  exact h

/-- If the original traversal exit occurs in a child, it is the child's
exit. -/
theorem piece_exit_eq_of_parent_exit_mem
    (S : ForwardContactSplit l X) (q : S.Piece)
    (hmem : l.exit ∈ q.1.support) : (S.pieceLink q).exit = l.exit := by
  have hfinish : l.path.finish ∈ q.1.support := by
    simpa only [Link.exit, S.direction_eq] using hmem
  have h := FinitePath.finish_eq_of_parent_finish_mem
    (S.piece_isSubpathOf q) hfinish
  change q.1.finish = l.exit
  rw [show l.exit = l.path.finish by simp only [Link.exit, S.direction_eq]]
  exact h

theorem every_contact_is_piece_endpoint (S : ForwardContactSplit l X) :
    l.path.support ∩ X ⊆
      {x | ∃ q : S.Piece, x = q.1.start ∨ x = q.1.finish} := by
  intro x hx
  obtain ⟨q, hq, hxq⟩ := S.split.every_contact_is_piece_endpoint hx
  exact ⟨⟨q, hq⟩, hxq⟩

theorem edgeSet_exact (S : ForwardContactSplit l X) :
    (⋃ q : S.Piece, q.1.edgeSet) = l.path.edgeSet := by
  rw [← S.split.edgeSet_exact]
  ext e
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨q, he⟩
    exact ⟨q.1, ⟨q.2, he⟩⟩
  · rintro ⟨q, hq, he⟩
    exact ⟨⟨q, hq⟩, he⟩

theorem vertexSet_exact (S : ForwardContactSplit l X) :
    (⋃ q : S.Piece, q.1.support) = l.path.support := by
  rw [← S.split.vertexSet_exact]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨q, hx⟩
    exact ⟨q.1, ⟨q.2, hx⟩⟩
  · rintro ⟨q, hq, hx⟩
    exact ⟨⟨q, hq⟩, hx⟩

/-- Construction of the forward-link split from the finite-path theorem. -/
theorem exists_of_direction_eq (l : Link D) (X : Set V)
    (hforward : l.direction = .forward) :
    Nonempty (ForwardContactSplit l X) := by
  obtain ⟨S⟩ := FinitePath.exists_contactSplit l.path X l.nontrivial
  exact ⟨⟨hforward, S⟩⟩

end ForwardContactSplit
end Link
end Alternating
end Erdos599
