/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingEdgeWalk
import ErdosProblems.Erdos599.AlternatingMacroFlatten
import ErdosProblems.Erdos599.OmegaListFlatten
import ErdosProblems.Erdos599.RawAlternatingDichotomy

/-!
# Provenance for chronological erasure of macro blocks

The flattened macro chain carries more information than its vertex stream:
every raw edge has a tagged macro member, that member has a colour, and its
underlying path belongs to the corresponding warp.  This file packages that
information and proves the two facts used after chronological loop erasure.

* two consecutive retained edges of the same colour have the same tagged
  macro member;
* if a compressed alternating trace uses every reference member in at most
  one backward link, its backward edges on that member form an edge interval.

The second statement is deliberately independent of the particular run
compressor.  The macro compiler only has to supply the unique-owner
certificate obtained from convexity of the raw member fibres.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u v w

variable {V : Type u} {Γ : DWeb V}

/-! ## Recovering vertex containment from nontrivial edge containment -/

private theorem walk_exists_outgoing_of_mem_support_of_ne_finish
    {D : Digraph V} : ∀ {a b x : V} (p : Walk D a b),
      x ∈ p.support → x ≠ b → ∃ y, (x, y) ∈ p.edgeSet
  | a, _, x, .nil, hx, hne => by
      have : x = a := by simpa using hx
      exact (hne this).elim
  | a, b, x, .cons (v := c) edge p, hx, hne => by
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨c, by simp⟩
      · obtain ⟨y, hy⟩ :=
          walk_exists_outgoing_of_mem_support_of_ne_finish p hx hne
        exact ⟨y, by simp [hy]⟩

private theorem walk_exists_incoming_of_mem_support_of_ne_start
    {D : Digraph V} : ∀ {a b x : V} (p : Walk D a b),
      x ∈ p.support → x ≠ a → ∃ y, (y, x) ∈ p.edgeSet
  | a, _, x, .nil, hx, hne => by
      have : x = a := by simpa using hx
      exact (hne this).elim
  | a, b, x, .cons (v := c) edge p, hx, hne => by
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact (hne rfl).elim
      · by_cases hxc : x = c
        · subst x
          exact ⟨a, by simp⟩
        · obtain ⟨y, hy⟩ :=
            walk_exists_incoming_of_mem_support_of_ne_start p hx hxc
          exact ⟨y, by simp [hy]⟩

/-- For a nontrivial finite path, containment of all directed edges in a
path already forces containment of all vertices.  This is the small bridge
needed by both macro compilers: their run compressors track raw edges, while
`FinitePath.IsSubpathOf` records both edges and vertices. -/
theorem finitePath_isSubpathOf_of_edgeSet_subset
    {D : Digraph V} (q : FinitePath D) (p : Path D)
    (hne : q.start ≠ q.finish) (hE : q.edgeSet ⊆ p.edgeSet) :
    q.IsSubpathOf p := by
  refine ⟨?_, hE⟩
  intro x hx
  by_cases hxf : x = q.finish
  · have hxs : x ≠ q.start := by
      intro h
      apply hne
      exact h.symm.trans hxf
    obtain ⟨y, hy⟩ :=
      walk_exists_incoming_of_mem_support_of_ne_start q.walk hx hxs
    exact (p.edgeSet_subset_support_prod (hE hy)).2
  · obtain ⟨y, hy⟩ :=
      walk_exists_outgoing_of_mem_support_of_ne_finish q.walk hx hxf
    exact (p.edgeSet_subset_support_prod (hE hy)).1

namespace OmegaBlocks

/-- Edge-level data retained by the full macro-block flattening.  `M` is a
tagged member type (in the application it distinguishes a `Z` occurrence
from a `Y` occurrence even if the two underlying paths happen to be equal).

`member_convex` says that the raw occurrences of one tagged macro member are
one integer interval.  The two edge-membership fields incorporate traversal
orientation: forward raw edges use the path orientation and backward raw
edges use its reverse. -/
structure EdgeProvenance (B : OmegaBlocks V) (Z Y : Set Γ.DPath)
    (M : Type v) where
  member : ℕ → M
  colour : M → Direction
  carrier : M → Γ.DPath
  carrier_injective_on_colour : ∀ {a b : M},
    colour a = colour b → carrier a = carrier b → a = b
  carrier_mem_forward : ∀ a, colour a = .forward → carrier a ∈ Z
  carrier_mem_backward : ∀ a, colour a = .backward → carrier a ∈ Y
  edge_mem_forward : ∀ k, colour (member k) = .forward →
    (B.rawVertex k, B.rawVertex (k + 1)) ∈ (carrier (member k)).edgeSet
  edge_mem_backward : ∀ k, colour (member k) = .backward →
    (B.rawVertex (k + 1), B.rawVertex k) ∈ (carrier (member k)).edgeSet
  member_convex : ∀ {i j k : ℕ}, i ≤ j → j ≤ k →
    member i = member k → member j = member i

namespace EdgeProvenance

variable {Z Y : Set Γ.DPath} {M : Type v} {B : OmegaBlocks V}

/-- A same-colour end-to-start join in the flattened stream can only occur
inside one tagged macro member.  Warp disjointness first identifies the two
underlying carriers; injectivity of the colour-tagged carrier map then
identifies the macro members themselves. -/
theorem member_eq_of_colour_eq_of_join
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    {i j : ℕ}
    (hcolour : P.colour (P.member i) = P.colour (P.member j))
    (hjoin : B.rawVertex (i + 1) = B.rawVertex j) :
    P.member i = P.member j := by
  cases hi : P.colour (P.member i) with
  | forward =>
      have hj : P.colour (P.member j) = .forward := hcolour.symm.trans hi
      have hei := P.edge_mem_forward i hi
      have hej := P.edge_mem_forward j hj
      have hxi : B.rawVertex (i + 1) ∈ (P.carrier (P.member i)).support :=
        ((P.carrier (P.member i)).edgeSet_subset_support_prod hei).2
      have hxj : B.rawVertex (i + 1) ∈ (P.carrier (P.member j)).support := by
        rw [hjoin]
        exact ((P.carrier (P.member j)).edgeSet_subset_support_prod hej).1
      have hcarrier : P.carrier (P.member i) = P.carrier (P.member j) :=
        DWeb.IsWarp.eq_of_mem_support hZ
          (P.carrier_mem_forward _ hi) (P.carrier_mem_forward _ hj) hxi hxj
      exact P.carrier_injective_on_colour hcolour hcarrier
  | backward =>
      have hj : P.colour (P.member j) = .backward := hcolour.symm.trans hi
      have hei := P.edge_mem_backward i hi
      have hej := P.edge_mem_backward j hj
      have hxi : B.rawVertex (i + 1) ∈ (P.carrier (P.member i)).support :=
        ((P.carrier (P.member i)).edgeSet_subset_support_prod hei).1
      have hxj : B.rawVertex (i + 1) ∈ (P.carrier (P.member j)).support := by
        rw [hjoin]
        exact ((P.carrier (P.member j)).edgeSet_subset_support_prod hej).2
      have hcarrier : P.carrier (P.member i) = P.carrier (P.member j) :=
        DWeb.IsWarp.eq_of_mem_support hY
          (P.carrier_mem_backward _ hi) (P.carrier_mem_backward _ hj) hxi hxj
      exact P.carrier_injective_on_colour hcolour hcarrier

/-- Consecutive edges retained by chronological loop erasure and having the
same colour come from the same tagged macro member. -/
theorem loopErasedIndex_member_eq_of_colour_eq
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite) (n : ℕ)
    (hcolour :
      P.colour (P.member (loopErasedIndex B.rawVertex hfinite n)) =
        P.colour (P.member
          (loopErasedIndex B.rawVertex hfinite (n + 1)))) :
    P.member (loopErasedIndex B.rawVertex hfinite n) =
      P.member (loopErasedIndex B.rawVertex hfinite (n + 1)) := by
  apply P.member_eq_of_colour_eq_of_join hZ hY hcolour
  exact loopErasedIndex_join B.rawVertex hfinite n

/-- Convex raw member fibres remain convex after restriction to the strictly
increasing chronological-erasure indices. -/
theorem loopErasedIndex_member_convex
    (P : B.EdgeProvenance Z Y M)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hik :
      P.member (loopErasedIndex B.rawVertex hfinite i) =
        P.member (loopErasedIndex B.rawVertex hfinite k)) :
    P.member (loopErasedIndex B.rawVertex hfinite j) =
      P.member (loopErasedIndex B.rawVertex hfinite i) := by
  exact P.member_convex
    ((loopErasedIndex_strictMono B.rawVertex hfinite).monotone hij)
    ((loopErasedIndex_strictMono B.rawVertex hfinite).monotone hjk) hik

/-- A retained macro member cannot disappear across an edge of another
colour and later reappear.  This is the direct input for proving injectivity
of the owner assigned to maximal backward runs. -/
theorem loopErasedIndex_member_ne_of_colour_between
    (P : B.EdgeProvenance Z Y M)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hcolour :
      P.colour (P.member (loopErasedIndex B.rawVertex hfinite j)) ≠
        P.colour (P.member (loopErasedIndex B.rawVertex hfinite i))) :
    P.member (loopErasedIndex B.rawVertex hfinite i) ≠
      P.member (loopErasedIndex B.rawVertex hfinite k) := by
  intro hik
  apply hcolour
  exact congrArg P.colour
    (P.loopErasedIndex_member_convex hfinite hij hjk hik)

/-- If every raw member has only finitely many edge occurrences, then the
colour along the chronologically loop-erased stream changes arbitrarily far
out.  Indeed, adjacent retained edges of one colour have the same member;
an eventually constant colour would therefore trap infinitely many strictly
increasing retained indices in one finite member fibre. -/
theorem exists_loopErasedIndex_colour_change
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfiniteVertex : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    (hfiniteMember : ∀ a : M, {k | P.member k = a}.Finite) (n : ℕ) :
    ∃ m, n < m ∧
      P.colour (P.member (loopErasedIndex B.rawVertex hfiniteVertex m)) ≠
        P.colour (P.member
          (loopErasedIndex B.rawVertex hfiniteVertex n)) := by
  by_contra hno
  push Not at hno
  have hcolour (k : ℕ) :
      P.colour (P.member
          (loopErasedIndex B.rawVertex hfiniteVertex (n + k))) =
        P.colour (P.member
          (loopErasedIndex B.rawVertex hfiniteVertex n)) := by
    by_cases hk : k = 0
    · subst k
      simp
    · exact hno (n + k) (by omega)
  have hmember (k : ℕ) :
      P.member (loopErasedIndex B.rawVertex hfiniteVertex (n + k)) =
        P.member (loopErasedIndex B.rawVertex hfiniteVertex n) := by
    induction k with
    | zero => simp
    | succ k ih =>
        apply Eq.trans ?_ ih
        apply (P.loopErasedIndex_member_eq_of_colour_eq hZ hY
          hfiniteVertex (n + k) ?_).symm
        simpa [Nat.add_assoc] using
          (hcolour k).trans (hcolour (k + 1)).symm
  have hinj : Function.Injective
      (fun k ↦ loopErasedIndex B.rawVertex hfiniteVertex (n + k)) :=
    fun _ _ h ↦ Nat.add_left_cancel
      ((loopErasedIndex_strictMono B.rawVertex hfiniteVertex).injective h)
  have hinfinite :
      {k | P.member k =
        P.member (loopErasedIndex B.rawVertex hfiniteVertex n)}.Infinite :=
    Set.infinite_of_injective_forall_mem hinj hmember
  exact hinfinite (hfiniteMember _)

/-- On a constant-colour interval of the loop-erased stream, every retained
edge has the same tagged member as the first one. -/
theorem loopErasedIndex_member_eq_of_colour_constant
    (P : B.EdgeProvenance Z Y M) (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hfinite : ∀ n, (occurrenceFiber B.rawVertex n).Finite)
    {a k : ℕ} (hak : a ≤ k)
    (hcolour : ∀ j, a ≤ j → j ≤ k →
      P.colour (P.member (loopErasedIndex B.rawVertex hfinite j)) =
        P.colour (P.member (loopErasedIndex B.rawVertex hfinite a))) :
    P.member (loopErasedIndex B.rawVertex hfinite k) =
      P.member (loopErasedIndex B.rawVertex hfinite a) := by
  induction k, hak using Nat.le_induction with
  | base => rfl
  | succ k hak ih =>
      have hadj :
          P.member (loopErasedIndex B.rawVertex hfinite k) =
            P.member (loopErasedIndex B.rawVertex hfinite (k + 1)) := by
        apply P.loopErasedIndex_member_eq_of_colour_eq hZ hY hfinite
        exact (hcolour k (by omega) (by omega)).trans
          (hcolour (k + 1) (by omega) le_rfl).symm
      exact hadj.symm.trans (ih fun j haj hjk ↦
        hcolour j haj (hjk.trans (Nat.le_succ k)))

end EdgeProvenance
end OmegaBlocks

namespace AltPath

/-- An index-friendly version of backward-link provenance.  Run compressors
already enumerate their links by `ℕ` or by a finite type, so this form avoids
dependent choices from membership in `Q.links`. -/
structure IndexedBackwardProvenance (Q : AltPath Γ.graph)
    (Y : Set Γ.DPath) (I : Type w) where
  link : I → Link Γ.graph
  links_eq_range : Q.links = Set.range link
  owner : ∀ i : I, (link i).direction = .backward → Γ.DPath
  owner_mem : ∀ (i : I) (hd : (link i).direction = .backward),
    owner i hd ∈ Y
  isSubpath : ∀ (i : I) (hd : (link i).direction = .backward),
    (link i).path.IsSubpathOf (owner i hd)
  owner_unique : ∀ (i j : I) (hi : (link i).direction = .backward)
    (hj : (link j).direction = .backward),
    owner i hi = owner j hj → link i = link j

namespace IndexedBackwardProvenance

variable {Y : Set Γ.DPath} {Q : AltPath Γ.graph} {I : Type w}

/-- Indexed unique-owner data proves the interval clause directly. -/
theorem isEdgeInterval
    (P : Q.IndexedBackwardProvenance Y I) (hY : Γ.IsWarp Y)
    (p : Γ.DPath) (hpY : p ∈ Y) :
    IsEdgeInterval (Q.directionEdges .backward ∩ p.edgeSet) p := by
  classical
  by_cases hex : ∃ (i : I) (hd : (P.link i).direction = .backward),
      P.owner i hd = p
  · rcases hex with ⟨i, hi, hip⟩
    right
    refine ⟨.inl (P.link i).path, ?_, ?_⟩
    · change (P.link i).path.IsSubpathOf p
      simpa [hip] using P.isSubpath i hi
    · apply Set.Subset.antisymm
      · rintro e ⟨heQ, hep⟩
        simp only [AltPath.directionEdges, Set.mem_iUnion] at heQ
        rcases heQ with ⟨l, hl, hd, hel⟩
        rw [P.links_eq_range] at hl
        rcases hl with ⟨j, rfl⟩
        have helOwner : e ∈ (P.owner j hd).edgeSet :=
          (P.isSubpath j hd).2 hel
        have howner : P.owner j hd = p :=
          DWeb.IsWarp.eq_of_mem_support hY (P.owner_mem j hd) hpY
            ((P.owner j hd).edgeSet_subset_support_prod helOwner).1
            (p.edgeSet_subset_support_prod hep).1
        have hji : P.link j = P.link i :=
          P.owner_unique j i hd hi (howner.trans hip.symm)
        simpa [hji] using hel
      · intro e hei
        constructor
        · simp only [AltPath.directionEdges, Set.mem_iUnion]
          refine ⟨P.link i, ?_, hi, hei⟩
          rw [P.links_eq_range]
          exact ⟨i, rfl⟩
        · have : e ∈ (P.owner i hi).edgeSet :=
            (P.isSubpath i hi).2 hei
          simpa [hip] using this
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases he with ⟨heQ, hep⟩
    simp only [AltPath.directionEdges, Set.mem_iUnion] at heQ
    rcases heQ with ⟨l, hl, hd, hel⟩
    rw [P.links_eq_range] at hl
    rcases hl with ⟨i, rfl⟩
    have helOwner : e ∈ (P.owner i hd).edgeSet :=
      (P.isSubpath i hd).2 hel
    have howner : P.owner i hd = p :=
      DWeb.IsWarp.eq_of_mem_support hY (P.owner_mem i hd) hpY
        ((P.owner i hd).edgeSet_subset_support_prod helOwner).1
        (p.edgeSet_subset_support_prod hep).1
    exact hex ⟨i, hd, howner⟩

/-- Indexed interval certificate for every member of the reference warp. -/
theorem intervals
    (P : Q.IndexedBackwardProvenance Y I) (hY : Γ.IsWarp Y) :
    ∀ p ∈ Y, IsEdgeInterval
      (Q.directionEdges .backward ∩ p.edgeSet) p := by
  intro p hp
  exact P.isEdgeInterval hY p hp

end IndexedBackwardProvenance

/-- Owner data for the backward links of an already compressed trace.  The
uniqueness field is exactly what raw member convexity gives: two backward
links cannot be fragments of the same tagged reference member. -/
structure BackwardLinkProvenance (Q : AltPath Γ.graph)
    (Y : Set Γ.DPath) where
  owner : ∀ (l : Link Γ.graph), l ∈ Q.links →
    l.direction = .backward → Γ.DPath
  owner_mem : ∀ (l : Link Γ.graph) (hl : l ∈ Q.links)
    (hd : l.direction = .backward), owner l hl hd ∈ Y
  isSubpath : ∀ (l : Link Γ.graph) (hl : l ∈ Q.links)
    (hd : l.direction = .backward), l.path.IsSubpathOf (owner l hl hd)
  owner_unique : ∀ (l : Link Γ.graph) (hl : l ∈ Q.links)
    (hd : l.direction = .backward) (r : Link Γ.graph) (hr : r ∈ Q.links)
    (rd : r.direction = .backward),
    owner l hl hd = owner r hr rd → l = r

namespace BackwardLinkProvenance

variable {Y : Set Γ.DPath} {Q : AltPath Γ.graph}

/-- Unique backward-link provenance gives the exact interval clause from
Definition 4.8.  If a reference member owns no link, the intersection is
empty.  Otherwise it is precisely the edge set of its unique link, which is
a finite subpath of that member. -/
theorem isEdgeInterval
    (P : Q.BackwardLinkProvenance Y) (hY : Γ.IsWarp Y)
    (p : Γ.DPath) (hpY : p ∈ Y) :
    IsEdgeInterval (Q.directionEdges .backward ∩ p.edgeSet) p := by
  classical
  by_cases hex : ∃ (l : Link Γ.graph) (hl : l ∈ Q.links)
      (hd : l.direction = .backward), P.owner l hl hd = p
  · rcases hex with ⟨l, hl, hd, hlp⟩
    right
    refine ⟨.inl l.path, ?_, ?_⟩
    · change l.path.IsSubpathOf p
      simpa [hlp] using P.isSubpath l hl hd
    · apply Set.Subset.antisymm
      · rintro e ⟨heQ, hep⟩
        simp only [AltPath.directionEdges, Set.mem_iUnion] at heQ
        rcases heQ with ⟨r, hr, rd, her⟩
        have herOwner : e ∈ (P.owner r hr rd).edgeSet :=
          (P.isSubpath r hr rd).2 her
        have howner : P.owner r hr rd = p :=
          DWeb.IsWarp.eq_of_mem_support hY (P.owner_mem r hr rd) hpY
            ((P.owner r hr rd).edgeSet_subset_support_prod herOwner).1
            (p.edgeSet_subset_support_prod hep).1
        have hrl : r = l :=
          P.owner_unique r hr rd l hl hd (howner.trans hlp.symm)
        simpa [hrl] using her
      · intro e hel
        constructor
        · simp only [AltPath.directionEdges, Set.mem_iUnion]
          exact ⟨l, hl, hd, hel⟩
        · have : e ∈ (P.owner l hl hd).edgeSet :=
            (P.isSubpath l hl hd).2 hel
          simpa [hlp] using this
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases he with ⟨heQ, hep⟩
    simp only [AltPath.directionEdges, Set.mem_iUnion] at heQ
    rcases heQ with ⟨l, hl, hd, hel⟩
    have helOwner : e ∈ (P.owner l hl hd).edgeSet :=
      (P.isSubpath l hl hd).2 hel
    have howner : P.owner l hl hd = p :=
      DWeb.IsWarp.eq_of_mem_support hY (P.owner_mem l hl hd) hpY
        ((P.owner l hl hd).edgeSet_subset_support_prod helOwner).1
        (p.edgeSet_subset_support_prod hep).1
    exact hex ⟨l, hl, hd, howner⟩

/-- The interval certificate simultaneously for every reference member. -/
theorem intervals
    (P : Q.BackwardLinkProvenance Y) (hY : Γ.IsWarp Y) :
    ∀ p ∈ Y, IsEdgeInterval
      (Q.directionEdges .backward ∩ p.edgeSet) p := by
  intro p hp
  exact P.isEdgeInterval hY p hp

end BackwardLinkProvenance
end AltPath

end Alternating
end Erdos599
