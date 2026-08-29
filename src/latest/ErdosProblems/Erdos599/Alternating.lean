/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Normalization

/-!
# Safe alternating paths

This file formalizes the alternating-link language of Section 4 of
Aharoni--Berger.  An alternating path is not represented by an ordinary
directed path: its backward links are traversed against their orientation.
The representation below packages the six finite/infinite shapes of
Definition 4.2 uniformly as an alternating sequence of links, including the
zero-link singleton path used at a finite endpoint.

The collision predicate is deliberately asymmetric.  In particular a later
forward link may pass through the interior of an earlier backward link.  This
is the exceptional case needed in the proof of Lemma 4.13.
-/

namespace Erdos599

open Set
open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}


namespace Alternating

/-! ## Alternating traces -/

/-- Whether a link is traversed with or against the orientation of the
ambient digraph. -/
inductive Direction
  | forward
  | backward
  deriving DecidableEq, Repr

/-- A nontrivial finite path, together with the direction in which the
alternating trace traverses it. -/
structure Link (D : Digraph V) where
  path : DirectedPath.FinitePath D
  direction : Direction
  nontrivial : path.start ≠ path.finish

namespace Link

/-- The vertex at which traversal of the link begins. -/
def entry (l : Link D) : V :=
  match l.direction with
  | .forward => l.path.start
  | .backward => l.path.finish

/-- The vertex at which traversal of the link ends. -/
def exit (l : Link D) : V :=
  match l.direction with
  | .forward => l.path.finish
  | .backward => l.path.start

/-- The two ambient endpoints, with no orientation imposed. -/
def endpoints (l : Link D) : Set V :=
  {l.path.start, l.path.finish}

/-- The internal vertices of a link. -/
def interior (l : Link D) : Set V :=
  l.path.support \ l.endpoints

@[simp]
theorem entry_mem_support (l : Link D) : l.entry ∈ l.path.support := by
  cases h : l.direction <;> simp [entry, h]

@[simp]
theorem exit_mem_support (l : Link D) : l.exit ∈ l.path.support := by
  cases h : l.direction <;> simp [exit, h]

theorem entry_ne_exit (l : Link D) : l.entry ≠ l.exit := by
  cases h : l.direction with
  | forward => simpa [entry, exit, h] using l.nontrivial
  | backward => simpa [entry, exit, h] using Ne.symm l.nontrivial

@[simp]
theorem endpoints_eq (l : Link D) :
    l.endpoints = {l.entry, l.exit} := by
  cases h : l.direction <;> simp [endpoints, entry, exit, h, pair_comm]

end Link

/-- The precise permitted intersections of two links appearing in this
order in an alternating trace.  This is Definition 4.2(4)--(6), rewritten
in terms of traversal order.

* Equal-direction links meet only at crossed endpoints.
* A forward link followed immediately by a backward link meets exactly at
  their joining vertex; a non-immediate later backward link is disjoint.
* A backward link followed immediately by a forward link may additionally
  meet internally; if they are not immediate, all meetings are internal.
-/
def CompatibleInOrder (adjacent : Prop) (l r : Link D) : Prop :=
  match l.direction, r.direction with
  | .forward, .forward =>
      ∀ ⦃v⦄, v ∈ l.path.support → v ∈ r.path.support →
        (v = l.entry ∧ v = r.exit) ∨ (v = l.exit ∧ v = r.entry)
  | .backward, .backward =>
      ∀ ⦃v⦄, v ∈ l.path.support → v ∈ r.path.support →
        (v = l.entry ∧ v = r.exit) ∨ (v = l.exit ∧ v = r.entry)
  | .forward, .backward =>
      (adjacent → l.path.support ∩ r.path.support = {l.exit}) ∧
        (¬ adjacent → Disjoint l.path.support r.path.support)
  | .backward, .forward =>
      (adjacent →
        ∀ ⦃v⦄, v ∈ l.path.support → v ∈ r.path.support →
          v = l.exit ∨ (v ∈ l.interior ∧ v ∈ r.interior)) ∧
        (¬ adjacent →
          l.path.support ∩ r.path.support ⊆ l.interior ∩ r.interior)

/-- A finite alternating trace.  `lastIndex = n` means that the trace has
`n+1` links, so it is definitionally nonempty. -/
structure FiniteTrace (D : Digraph V) where
  lastIndex : ℕ
  link : Fin (lastIndex + 1) → Link D
  joins : ∀ i : Fin lastIndex,
    (link (Fin.castSucc i)).exit = (link i.succ).entry
  alternates : ∀ i : Fin lastIndex,
    (link (Fin.castSucc i)).direction ≠ (link i.succ).direction
  compatible : ∀ (i j : Fin (lastIndex + 1)), i < j →
    CompatibleInOrder (j.1 = i.1 + 1) (link i) (link j)

namespace FiniteTrace

/-- The one-link finite alternating trace. -/
def singleton (l : Link D) : FiniteTrace D where
  lastIndex := 0
  link := fun _ ↦ l
  joins := fun i ↦ Fin.elim0 i
  alternates := fun i ↦ Fin.elim0 i
  compatible := by
    intro i j hij
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst i
    subst j
    simp at hij

def firstLink (Q : FiniteTrace D) : Link D :=
  Q.link ⟨0, Nat.zero_lt_succ _⟩

def lastLink (Q : FiniteTrace D) : Link D :=
  Q.link ⟨Q.lastIndex, Nat.lt_succ_self _⟩

def initial (Q : FiniteTrace D) : V := Q.firstLink.entry

def terminal (Q : FiniteTrace D) : V := Q.lastLink.exit

def links (Q : FiniteTrace D) : Set (Link D) := Set.range Q.link

def vertexSet (Q : FiniteTrace D) : Set V :=
  ⋃ i, (Q.link i).path.support

def edgeSet (Q : FiniteTrace D) : Set (V × V) :=
  ⋃ i, (Q.link i).path.edgeSet

@[simp]
theorem firstLink_singleton (l : Link D) : (singleton l).firstLink = l :=
  rfl

@[simp]
theorem lastLink_singleton (l : Link D) : (singleton l).lastLink = l :=
  rfl

@[simp]
theorem initial_singleton (l : Link D) : (singleton l).initial = l.entry :=
  rfl

@[simp]
theorem terminal_singleton (l : Link D) : (singleton l).terminal = l.exit :=
  rfl

@[simp]
theorem vertexSet_singleton (l : Link D) :
    (singleton l).vertexSet = l.path.support := by
  ext v
  simp [vertexSet, singleton]

@[simp]
theorem edgeSet_singleton (l : Link D) :
    (singleton l).edgeSet = l.path.edgeSet := by
  ext e
  simp [edgeSet, singleton]

@[simp]
theorem firstLink_mem_links (Q : FiniteTrace D) : Q.firstLink ∈ Q.links :=
  ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩

@[simp]
theorem lastLink_mem_links (Q : FiniteTrace D) : Q.lastLink ∈ Q.links :=
  ⟨⟨Q.lastIndex, Nat.lt_succ_self _⟩, rfl⟩

theorem initial_mem_vertexSet (Q : FiniteTrace D) : Q.initial ∈ Q.vertexSet := by
  refine Set.mem_iUnion.2 ⟨⟨0, Nat.zero_lt_succ _⟩, ?_⟩
  exact Q.firstLink.entry_mem_support

theorem terminal_mem_vertexSet (Q : FiniteTrace D) : Q.terminal ∈ Q.vertexSet := by
  refine Set.mem_iUnion.2 ⟨⟨Q.lastIndex, Nat.lt_succ_self _⟩, ?_⟩
  exact Q.lastLink.exit_mem_support

end FiniteTrace

/-- An infinite alternating trace. -/
structure InfiniteTrace (D : Digraph V) where
  link : ℕ → Link D
  joins : ∀ i, (link i).exit = (link (i + 1)).entry
  alternates : ∀ i, (link i).direction ≠ (link (i + 1)).direction
  compatible : ∀ i j, i < j →
    CompatibleInOrder (j = i + 1) (link i) (link j)

namespace InfiniteTrace

def initial (Q : InfiniteTrace D) : V := (Q.link 0).entry

def links (Q : InfiniteTrace D) : Set (Link D) := Set.range Q.link

def vertexSet (Q : InfiniteTrace D) : Set V :=
  ⋃ i, (Q.link i).path.support

def edgeSet (Q : InfiniteTrace D) : Set (V × V) :=
  ⋃ i, (Q.link i).path.edgeSet

@[simp]
theorem firstLink_mem_links (Q : InfiniteTrace D) : Q.link 0 ∈ Q.links :=
  ⟨0, rfl⟩

theorem initial_mem_vertexSet (Q : InfiniteTrace D) : Q.initial ∈ Q.vertexSet := by
  refine Set.mem_iUnion.2 ⟨0, ?_⟩
  exact (Q.link 0).entry_mem_support

end InfiniteTrace

/-- The trivial, nontrivial finite, and infinite cases of an alternating
path.  The zero-link case is source Definition 4.2(iii) with `k = 0`; it is
essential when a warp contains a singleton path. -/
inductive AltPath (D : Digraph V)
  | trivial (vertex : V)
  | finite (trace : FiniteTrace D)
  | infinite (trace : InfiniteTrace D)

namespace AltPath

/-- Regard one nontrivial directed link as a finite alternating path. -/
def single (l : Link D) : AltPath D :=
  .finite (FiniteTrace.singleton l)

def links : AltPath D → Set (Link D)
  | .trivial _ => ∅
  | .finite Q => Q.links
  | .infinite Q => Q.links

def initial : AltPath D → V
  | .trivial v => v
  | .finite Q => Q.initial
  | .infinite Q => Q.initial

def terminal? : AltPath D → Option V
  | .trivial v => some v
  | .finite Q => some Q.terminal
  | .infinite _ => none

def vertexSet : AltPath D → Set V
  | .trivial v => {v}
  | .finite Q => Q.vertexSet
  | .infinite Q => Q.vertexSet

def edgeSet : AltPath D → Set (V × V)
  | .trivial _ => ∅
  | .finite Q => Q.edgeSet
  | .infinite Q => Q.edgeSet

def firstDirection? : AltPath D → Option Direction
  | .trivial _ => none
  | .finite Q => some Q.firstLink.direction
  | .infinite Q => some (Q.link 0).direction

def lastDirection? : AltPath D → Option Direction
  | .trivial _ => none
  | .finite Q => some Q.lastLink.direction
  | .infinite _ => none

def IsFinite : AltPath D → Prop
  | .trivial _ => True
  | .finite _ => True
  | .infinite _ => False

def IsInfinite : AltPath D → Prop
  | .trivial _ => False
  | .finite _ => False
  | .infinite _ => True

@[simp]
theorem links_single (l : Link D) : (single l).links = {l} := by
  ext k
  simp [single, links, FiniteTrace.links, FiniteTrace.singleton]

@[simp]
theorem initial_single (l : Link D) : (single l).initial = l.entry :=
  rfl

@[simp]
theorem terminal?_single (l : Link D) : (single l).terminal? = some l.exit :=
  rfl

@[simp]
theorem vertexSet_single (l : Link D) : (single l).vertexSet = l.path.support :=
  FiniteTrace.vertexSet_singleton l

@[simp]
theorem edgeSet_single (l : Link D) : (single l).edgeSet = l.path.edgeSet :=
  FiniteTrace.edgeSet_singleton l

@[simp]
theorem firstDirection?_single (l : Link D) :
    (single l).firstDirection? = some l.direction :=
  rfl

@[simp]
theorem lastDirection?_single (l : Link D) :
    (single l).lastDirection? = some l.direction :=
  rfl

@[simp]
theorem isFinite_single (l : Link D) : (single l).IsFinite :=
  True.intro

@[simp]
theorem not_isInfinite_single (l : Link D) : ¬ (single l).IsInfinite := by
  simp [single, IsInfinite]

@[simp]
theorem links_trivial (v : V) : (AltPath.trivial v : AltPath D).links = ∅ :=
  rfl

@[simp]
theorem initial_trivial (v : V) : (AltPath.trivial v : AltPath D).initial = v :=
  rfl

@[simp]
theorem terminal?_trivial (v : V) :
    (AltPath.trivial v : AltPath D).terminal? = some v :=
  rfl

@[simp]
theorem vertexSet_trivial (v : V) :
    (AltPath.trivial v : AltPath D).vertexSet = {v} :=
  rfl

@[simp]
theorem edgeSet_trivial (v : V) :
    (AltPath.trivial v : AltPath D).edgeSet = ∅ :=
  rfl

@[simp]
theorem firstDirection?_trivial (v : V) :
    (AltPath.trivial v : AltPath D).firstDirection? = none :=
  rfl

@[simp]
theorem lastDirection?_trivial (v : V) :
    (AltPath.trivial v : AltPath D).lastDirection? = none :=
  rfl

@[simp]
theorem isFinite_trivial (v : V) : (AltPath.trivial v : AltPath D).IsFinite :=
  True.intro

@[simp]
theorem not_isInfinite_trivial (v : V) :
    ¬ (AltPath.trivial v : AltPath D).IsInfinite := by
  simp [IsInfinite]

@[simp]
theorem terminal?_finite (Q : FiniteTrace D) :
    (AltPath.finite Q).terminal? = some Q.terminal :=
  rfl

@[simp]
theorem terminal?_infinite (Q : InfiniteTrace D) :
    (AltPath.infinite Q).terminal? = none :=
  rfl

theorem isFinite_iff_exists_terminal (Q : AltPath D) :
    Q.IsFinite ↔ ∃ v, Q.terminal? = some v := by
  cases Q with
  | trivial v => exact ⟨fun _ ↦ ⟨v, rfl⟩, fun _ ↦ True.intro⟩
  | finite Q => exact ⟨fun _ ↦ ⟨Q.terminal, rfl⟩, fun _ ↦ True.intro⟩
  | infinite Q => simp [IsFinite, terminal?]

theorem isInfinite_iff_terminal?_eq_none (Q : AltPath D) :
    Q.IsInfinite ↔ Q.terminal? = none := by
  cases Q <;> simp [IsInfinite, terminal?]

theorem isInfinite_iff_not_isFinite (Q : AltPath D) :
    Q.IsInfinite ↔ ¬ Q.IsFinite := by
  cases Q <;> simp [IsInfinite, IsFinite]

theorem initial_mem_vertexSet (Q : AltPath D) : Q.initial ∈ Q.vertexSet := by
  cases Q with
  | trivial v => simp [initial, vertexSet]
  | finite Q => exact Q.initial_mem_vertexSet
  | infinite Q => exact Q.initial_mem_vertexSet

theorem edgeSet_subset_adj (Q : AltPath D) :
    Q.edgeSet ⊆ {e | D.Adj e.1 e.2} := by
  cases Q with
  | trivial v => simp [edgeSet]
  | finite Q =>
      rintro e he
      simp only [edgeSet, FiniteTrace.edgeSet, Set.mem_iUnion] at he
      rcases he with ⟨i, hi⟩
      exact (Q.link i).path.edgeSet_subset_adj hi
  | infinite Q =>
      rintro e he
      simp only [edgeSet, InfiniteTrace.edgeSet, Set.mem_iUnion] at he
      rcases he with ⟨i, hi⟩
      exact (Q.link i).path.edgeSet_subset_adj hi

theorem edgeSet_eq_iUnion_links (Q : AltPath D) :
    Q.edgeSet = ⋃ l ∈ Q.links, l.path.edgeSet := by
  ext e
  cases Q with
  | trivial v => simp [edgeSet, links]
  | finite Q =>
      simp only [edgeSet, FiniteTrace.edgeSet, links, FiniteTrace.links,
        Set.mem_iUnion, Set.mem_range]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨Q.link i, ⟨i, rfl⟩, hi⟩
      · rintro ⟨l, ⟨i, rfl⟩, hi⟩
        exact ⟨i, hi⟩
  | infinite Q =>
      simp only [edgeSet, InfiniteTrace.edgeSet, links, InfiniteTrace.links,
        Set.mem_iUnion, Set.mem_range]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨Q.link i, ⟨i, rfl⟩, hi⟩
      · rintro ⟨l, ⟨i, rfl⟩, hi⟩
        exact ⟨i, hi⟩

/-- Edges of links traversed in a specified direction. -/
def directionEdges (Q : AltPath D) (d : Direction) : Set (V × V) :=
  ⋃ l ∈ Q.links, ⋃ (_ : l.direction = d), l.path.edgeSet

theorem edgeSet_eq_directionEdges_union (Q : AltPath D) :
    Q.edgeSet = Q.directionEdges .forward ∪ Q.directionEdges .backward := by
  rw [Q.edgeSet_eq_iUnion_links]
  ext e
  simp only [directionEdges, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨l, hl, he⟩
    cases hdir : l.direction with
    | forward => exact Or.inl ⟨l, hl, hdir, he⟩
    | backward => exact Or.inr ⟨l, hl, hdir, he⟩
  · rintro (⟨l, hl, _hdir, he⟩ | ⟨l, hl, _hdir, he⟩)
    · exact ⟨l, hl, he⟩
    · exact ⟨l, hl, he⟩

/-- Vertices occurring on links traversed in a specified direction. -/
def directionVertices (Q : AltPath D) (d : Direction) : Set V :=
  ⋃ l ∈ Q.links, ⋃ (_ : l.direction = d), l.path.support

end AltPath

/-! ## Core-bound alternating-path predicates -/

variable {Γ : DWeb V}

end Alternating

namespace Alternating

variable {V : Type u} {Γ : DWeb V}

theorem DWeb.IsWarp.eq_of_mem_support {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) {p q : Γ.DPath} (hp : p ∈ W) (hq : q ∈ W)
    {x : V} (hxp : x ∈ p.support) (hxq : x ∈ q.support) : p = q := by
  by_contra hpq
  exact Set.disjoint_left.1 (DWeb.IsWarp.disjoint Γ hW hp hq hpq) hxp hxq

/-- The unique member of a warp containing a specified covered vertex. -/
noncomputable def DWeb.IsWarp.pathAt {W : Set Γ.DPath}
    (_hW : Γ.IsWarp W) {x : V} (hx : x ∈ Γ.vertexSet W) : Γ.DPath :=
  Classical.choose hx

theorem DWeb.IsWarp.pathAt_mem {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) {x : V} (hx : x ∈ Γ.vertexSet W) :
    DWeb.IsWarp.pathAt hW hx ∈ W :=
  (Classical.choose_spec hx).1

theorem DWeb.IsWarp.mem_support_pathAt {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) {x : V} (hx : x ∈ Γ.vertexSet W) :
    x ∈ (DWeb.IsWarp.pathAt hW hx).support :=
  (Classical.choose_spec hx).2

theorem DWeb.IsWarp.eq_pathAt_of_mem_support {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) {x : V} (hx : x ∈ Γ.vertexSet W)
    {p : Γ.DPath} (hp : p ∈ W) (hxp : x ∈ p.support) :
    p = DWeb.IsWarp.pathAt hW hx :=
  DWeb.IsWarp.eq_of_mem_support hW hp (DWeb.IsWarp.pathAt_mem hW hx) hxp
    (DWeb.IsWarp.mem_support_pathAt hW hx)

theorem DWeb.HasFiniteCharacter.exists_finitePath
    {W : Set Γ.DPath} (hW : Γ.HasFiniteCharacter W)
    {p : Γ.DPath} (hp : p ∈ W) :
    ∃ q : DirectedPath.FinitePath Γ.graph, p = .inl q :=
  hW hp

/-- The union of the directed edge sets of a path family. -/
def familyEdges (W : Set Γ.DPath) : Set (V × V) :=
  ⋃ p ∈ W, p.edgeSet

theorem familyEdges_subset_adj (W : Set Γ.DPath) :
    familyEdges W ⊆ {e | Γ.graph.Adj e.1 e.2} := by
  rintro e he
  simp only [familyEdges, Set.mem_iUnion] at he
  rcases he with ⟨p, _hpW, hp⟩
  exact p.edgeSet_subset_adj hp

/-- A finite path is a fragment of some member of `W`. -/
def IsFragmentOf (q : DirectedPath.FinitePath Γ.graph) (W : Set Γ.DPath) : Prop :=
  ∃ p ∈ W, q.IsSubpathOf p

/-- Every backward link is a fragment of the reference warp, as required by
Definition 4.2. -/
def BackwardLinksOn (Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  ∀ l ∈ Q.links, l.direction = .backward → IsFragmentOf l.path Y

/-- Forward links do not use an edge of the reference warp.  This is the
identity `E[Q] ∩ E(P) = ⋃ E(Rᵢ) ∩ E(P)` used explicitly in Definition 4.8. -/
def ForwardLinksOff (Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  ∀ l ∈ Q.links, l.direction = .forward →
    Disjoint l.path.edgeSet (familyEdges Y)

/-- Every meeting of a forward link with the reference warp is represented
by a backward link of the same alternating path.  This is an additional
maximal-contact normalization used by the switching-ready development; it is
not a conjunct of the published Definition 4.2, which allows forward links
to meet `V[Y]`.  The qualification "new" is essential, since a later forward
link may pass through the interior of an earlier backward link. -/
def ForwardVertexContactsCovered (Y : Set Γ.DPath)
    (Q : AltPath Γ.graph) : Prop :=
  Q.directionVertices .forward ∩ Γ.vertexSet Y ⊆
    Q.directionVertices .backward

theorem ForwardLinksOff.directionEdges_disjoint
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph} (h : ForwardLinksOff Y Q) :
    Disjoint (Q.directionEdges .forward) (familyEdges Y) := by
  rw [Set.disjoint_left]
  intro e heQ heY
  simp only [AltPath.directionEdges, Set.mem_iUnion] at heQ
  rcases heQ with ⟨l, hl, hdir, hel⟩
  exact Set.disjoint_left.1 (h l hl hdir) hel heY

theorem ForwardLinksOff.edgeSet_inter_familyEdges
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph} (h : ForwardLinksOff Y Q) :
    Q.edgeSet ∩ familyEdges Y =
      Q.directionEdges .backward ∩ familyEdges Y := by
  rw [Q.edgeSet_eq_directionEdges_union, Set.union_inter_distrib_right]
  have hempty : Q.directionEdges .forward ∩ familyEdges Y = ∅ :=
    Set.disjoint_iff_inter_eq_empty.1 h.directionEdges_disjoint
  rw [hempty, Set.empty_union]

/-- A `Y`-alternating path.  This is the literal source-level predicate used
by Definition 4.2 and Lemma 4.13: backward links lie on `Y`, and the two
exposed endpoints lie off `Y` when their adjacent link is forward.

The paper makes forward/reference edges disjoint only after replacing common
edge *occurrences* by parallel copies.  A plain `Digraph` relation cannot
represent those copies, so edge-disjointness is not imposed on this literal
predicate.  It is retained below as an explicit switching-ready certificate,
together with the extra contact condition needed to repair Lemma 4.9. -/
def IsAlternating (Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  Γ.IsWarp Y ∧ BackwardLinksOn Y Q ∧
    (Q.firstDirection? = some .forward → Q.initial ∉ Γ.vertexSet Y) ∧
    (∀ t, Q.terminal? = some t → Q.lastDirection? = some .forward →
      t ∉ Γ.vertexSet Y)

/-- The two additional certificates needed by the exact switching theorem:
forward links use no reference edge, and every reference-warp vertex met by a
forward link is also represented on a backward link. -/
def IsSwitchingAlternating (Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  IsAlternating Y Q ∧ ForwardLinksOff Y Q ∧
    ForwardVertexContactsCovered Y Q

theorem IsSwitchingAlternating.isAlternating
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingAlternating Y Q) : IsAlternating Y Q :=
  h.1

theorem IsSwitchingAlternating.forwardLinksOff
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingAlternating Y Q) : ForwardLinksOff Y Q :=
  h.2.1

theorem IsSwitchingAlternating.contactsCovered
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingAlternating Y Q) : ForwardVertexContactsCovered Y Q :=
  h.2.2

/-- A `[U,Y]`-alternating path: its forward links are fragments of `U`. -/
def IsBracketAlternating (U Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  IsAlternating Y Q ∧
    ∀ l ∈ Q.links, l.direction = .forward → IsFragmentOf l.path U

/-- A bracket alternating path together with the contact normalization used
by the corrected switching lemma. -/
def IsBracketSwitchingAlternating
    (U Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  IsBracketAlternating U Y Q ∧ ForwardLinksOff Y Q ∧
    ForwardVertexContactsCovered Y Q

theorem IsBracketSwitchingAlternating.isBracketAlternating
    {U Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsBracketSwitchingAlternating U Y Q) :
    IsBracketAlternating U Y Q :=
  h.1

theorem IsBracketSwitchingAlternating.forwardLinksOff
    {U Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsBracketSwitchingAlternating U Y Q) : ForwardLinksOff Y Q :=
  h.2.1

theorem IsBracketSwitchingAlternating.contactsCovered
    {U Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsBracketSwitchingAlternating U Y Q) :
    ForwardVertexContactsCovered Y Q :=
  h.2.2

theorem IsBracketSwitchingAlternating.isSwitchingAlternating
    {U Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsBracketSwitchingAlternating U Y Q) :
    IsSwitchingAlternating Y Q :=
  ⟨h.1.1, h.2.1, h.2.2⟩

/-- The optional extra commitment condition of Definition 4.4. -/
def IsCommitted (U : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  ∀ l ∈ Q.links, l.direction = .backward →
    Disjoint l.interior (Γ.vertexSet U \ Γ.terminalFrontier U)

/-- A leaving alternating path is infinite, or has its finite terminal
outside the reference warp. -/
def IsLeaving (Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  Q.IsInfinite ∨ ∃ t, Q.terminal? = some t ∧ t ∉ Γ.vertexSet Y

/-- An `A`-starting alternating path begins with a forward link at a vertex
of `A`.  The endpoint condition in `IsAlternating` then forces that vertex
outside the reference warp. -/
def IsStartingAt (A : Set V) (Q : AltPath Γ.graph) : Prop :=
  Q.firstDirection? = some .forward ∧ Q.initial ∈ A

/-- An augmenting alternating path in a web starts forward at an uncovered
source and ends forward at an uncovered target. -/
def IsAugmenting (Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  IsAlternating Y Q ∧ IsStartingAt Γ.source Q ∧
    ∃ t ∈ Γ.target, Q.terminal? = some t ∧ t ∉ Γ.vertexSet Y

/-- The edge relation obtained by applying an alternating path to a warp. -/
def switchedEdges (Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Set (V × V) :=
  (familyEdges Y \ Q.edgeSet) ∪ (Q.edgeSet \ familyEdges Y)

/-- Symmetric difference of edge sets, separated out because applying an
alternating path is an instance of this Boolean operation. -/
def edgeSymmDiff (E F : Set (V × V)) : Set (V × V) :=
  (E \ F) ∪ (F \ E)

@[simp]
theorem mem_edgeSymmDiff {E F : Set (V × V)} {e : V × V} :
    e ∈ edgeSymmDiff E F ↔ (e ∈ E ∧ e ∉ F) ∨ (e ∈ F ∧ e ∉ E) :=
  Iff.rfl

theorem edgeSymmDiff_comm (E F : Set (V × V)) :
    edgeSymmDiff E F = edgeSymmDiff F E := by
  ext e
  simp only [mem_edgeSymmDiff]
  tauto

@[simp]
theorem edgeSymmDiff_empty (E : Set (V × V)) : edgeSymmDiff E ∅ = E := by
  ext e
  simp

@[simp]
theorem empty_edgeSymmDiff (E : Set (V × V)) : edgeSymmDiff ∅ E = E := by
  rw [edgeSymmDiff_comm, edgeSymmDiff_empty]

@[simp]
theorem edgeSymmDiff_self (E : Set (V × V)) : edgeSymmDiff E E = ∅ := by
  ext e
  simp

theorem edgeSymmDiff_assoc (E F H : Set (V × V)) :
    edgeSymmDiff (edgeSymmDiff E F) H = edgeSymmDiff E (edgeSymmDiff F H) := by
  ext e
  simp only [mem_edgeSymmDiff]
  tauto

@[simp]
theorem edgeSymmDiff_cancel_right (E F : Set (V × V)) :
    edgeSymmDiff (edgeSymmDiff E F) F = E := by
  rw [edgeSymmDiff_assoc, edgeSymmDiff_self, edgeSymmDiff_empty]

theorem switchedEdges_eq_edgeSymmDiff (Y : Set Γ.DPath)
    (Q : AltPath Γ.graph) :
    switchedEdges Y Q = edgeSymmDiff (familyEdges Y) Q.edgeSet :=
  rfl

/-- Applying the same alternating edge set twice restores the original
edge relation.  This is the set-theoretic core of switching. -/
theorem switchedEdges_involutive (Y : Set Γ.DPath)
    (Q : AltPath Γ.graph) :
    edgeSymmDiff (switchedEdges Y Q) Q.edgeSet = familyEdges Y := by
  rw [switchedEdges_eq_edgeSymmDiff, edgeSymmDiff_cancel_right]

/-- Vertices represented by singleton paths in a path family.  The edge set
alone cannot remember these components. -/
def isolatedVertices (W : Set Γ.DPath) : Set V :=
  {v | Γ.trivialPath v ∈ W}

/-- A simple directed cycle written cyclically on `Fin n`. -/
structure DirectedCycle (V : Type u) where
  length : ℕ
  positive : 0 < length
  vertex : Fin length → V
  injective : Function.Injective vertex

namespace DirectedCycle

def next (C : DirectedCycle V) (i : Fin C.length) : Fin C.length :=
  ⟨(i.1 + 1) % C.length, Nat.mod_lt _ C.positive⟩

def EdgeSet (C : DirectedCycle V) : Set (V × V) :=
  {e | ∃ i, e = (C.vertex i, C.vertex (C.next i))}

def support (C : DirectedCycle V) : Set V :=
  Set.range C.vertex

end DirectedCycle

/-- A source cyclowarp is genuinely a set of pairwise vertex-disjoint path
and directed-cycle components (Section 2.4), not merely an arbitrary edge
relation.  Singleton components occur only among `paths`, so their ISO data is
determined by the component family. -/
structure Cyclowarp (Γ : DWeb V) where
  paths : Set Γ.DPath
  cycles : Set (DirectedCycle V)
  paths_isWarp : Γ.IsWarp paths
  cycles_in_graph : ∀ C ∈ cycles, C.EdgeSet ⊆ {e | Γ.graph.Adj e.1 e.2}
  cycles_disjoint : cycles.PairwiseDisjoint DirectedCycle.support
  paths_cycles_disjoint :
    ∀ p ∈ paths, ∀ C ∈ cycles, Disjoint p.support C.support

namespace Cyclowarp

/-- The edge set of all path and cycle components. -/
def edges (C : Cyclowarp Γ) : Set (V × V) :=
  familyEdges C.paths ∪ ⋃ c ∈ C.cycles, c.EdgeSet

/-- The singleton-path components of a cyclowarp. -/
def isolated (C : Cyclowarp Γ) : Set V :=
  isolatedVertices C.paths

/-- The paper's `C^path`, obtained by discarding all cycle components. -/
def pathPart (C : Cyclowarp Γ) : Set Γ.DPath :=
  C.paths

theorem pathPart_isWarp (C : Cyclowarp Γ) : Γ.IsWarp C.pathPart :=
  C.paths_isWarp

end Cyclowarp

/-- Raw edge and ISO data of applying an alternating path.  Unlike the old
encoding of `Cyclowarp`, this type makes no false structural promise: proving
that these data decompose into disjoint paths and cycles is a separate fact. -/
structure SwitchData (Γ : DWeb V) where
  edges : Set (V × V)
  edges_in_graph : edges ⊆ {e | Γ.graph.Adj e.1 e.2}
  isolated : Set V

namespace Cyclowarp

/-- Raw application data for source Definition 4.3.  The component theorem
`SwitchData.IsCyclowarp` records that this data is an honest cyclowarp. -/
def application (Y : Set Γ.DPath) (Q : AltPath Γ.graph) : SwitchData Γ where
  edges := switchedEdges Y Q
  edges_in_graph := by
    intro e he
    rcases he with he | he
    · exact familyEdges_subset_adj Y he.1
    · exact Q.edgeSet_subset_adj he.1
  isolated := isolatedVertices Y

@[simp]
theorem application_edges (Y : Set Γ.DPath) (Q : AltPath Γ.graph) :
    (application Y Q).edges = switchedEdges Y Q :=
  rfl

@[simp]
theorem application_isolated (Y : Set Γ.DPath) (Q : AltPath Γ.graph) :
    (application Y Q).isolated = isolatedVertices Y :=
  rfl

end Cyclowarp

namespace SwitchData

/-- A raw switched family is structurally a cyclowarp when its edge and ISO
data are realized by genuine disjoint path/cycle components. -/
def IsCyclowarp (S : SwitchData Γ) : Prop :=
  ∃ C : Cyclowarp Γ, C.edges = S.edges ∧ C.isolated = S.isolated

/-- An honest warp realizes raw application data when it has exactly its
edges and singleton components. -/
def RealizedBy (S : SwitchData Γ) (W : Set Γ.DPath) : Prop :=
  Γ.IsWarp W ∧ familyEdges W = S.edges ∧ isolatedVertices W = S.isolated

/-- A finite path is a component fragment of switched data.  For a zero-edge
path its vertex must be one of the explicitly retained singleton components. -/
def ContainsFinitePath (S : SwitchData Γ)
    (p : DirectedPath.FinitePath Γ.graph) : Prop :=
  p.edgeSet ⊆ S.edges ∧ (p.start ≠ p.finish ∨ p.start ∈ S.isolated)

/-- A ray is contained in switched data when all of its edges occur there. -/
def ContainsRay (S : SwitchData Γ) (r : DirectedPath.Ray Γ.graph) : Prop :=
  r.edgeSet ⊆ S.edges

/-- The exact conclusion of safe switching, Lemma 4.9. -/
def HasFiniteWarpRealization (S : SwitchData Γ) : Prop :=
  ∃ W : Set Γ.DPath, S.RealizedBy W ∧ Γ.HasFiniteCharacter W

theorem isCyclowarp_of_realizedBy {S : SwitchData Γ} {W : Set Γ.DPath}
    (h : S.RealizedBy W) : S.IsCyclowarp := by
  refine ⟨⟨W, ∅, h.1, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp
  · simp
  · simp
  · simpa [Cyclowarp.edges] using h.2.1
  · simpa [Cyclowarp.isolated] using h.2.2

end SwitchData

/-! ## Cycles, rays, and safeness -/

/-- A simple one-way infinite directed edge sequence. -/
structure DirectedRay (V : Type u) where
  vertex : ℕ → V
  injective : Function.Injective vertex

namespace DirectedRay

def EdgeSet (R : DirectedRay V) : Set (V × V) :=
  {e | ∃ i, e = (R.vertex i, R.vertex (i + 1))}

end DirectedRay

def ContainsDirectedCycle (E : Set (V × V)) : Prop :=
  ∃ C : DirectedCycle V, C.EdgeSet ⊆ E

def ContainsDirectedRay (E : Set (V × V)) : Prop :=
  ∃ R : DirectedRay V, R.EdgeSet ⊆ E

/-- A set of edges is one interval on a path.  The empty intersection is
allowed; otherwise it must be exactly the edge set of a finite path or ray
subpath.  The ray case matters for Definition 4.8 before finite character is
assumed. -/
def IsEdgeInterval (E : Set (V × V)) (p : Γ.DPath) : Prop :=
  E = ∅ ∨ ∃ q : Γ.DPath, q.IsSubpathOf p ∧ E = q.edgeSet

/-- Definition 4.8: backward-link edges used on each reference path form one
interval, while all alternating-path edges outside the reference warp contain
neither a ray nor a directed cycle.  Referring explicitly to backward-link
edges is essential before the paper's parallel-copy reduction. -/
def IsSafe (Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  IsAlternating Y Q ∧
    (∀ p ∈ Y,
      IsEdgeInterval (Q.directionEdges .backward ∩ p.edgeSet) p) ∧
    ¬ ContainsDirectedRay (Q.edgeSet \ familyEdges Y) ∧
    ¬ ContainsDirectedCycle (Q.edgeSet \ familyEdges Y)

/-- Source safeness plus both switching-ready certificates required for an
exact warp realization of the switched edge relation. -/
def IsSwitchingSafe (Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  IsSafe Y Q ∧ ForwardLinksOff Y Q ∧
    ForwardVertexContactsCovered Y Q

theorem IsSwitchingSafe.isSafe
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingSafe Y Q) : IsSafe Y Q :=
  h.1

theorem IsSwitchingSafe.forwardLinksOff
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingSafe Y Q) : ForwardLinksOff Y Q :=
  h.2.1

theorem IsSwitchingSafe.contactsCovered
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingSafe Y Q) : ForwardVertexContactsCovered Y Q :=
  h.2.2

theorem IsSwitchingSafe.isSwitchingAlternating
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingSafe Y Q) : IsSwitchingAlternating Y Q :=
  ⟨h.1.1, h.2.1, h.2.2⟩

/-- A safe `[U,Y]`-alternating path. -/
def IsBracketSafe (U Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  IsSafe Y Q ∧ IsBracketAlternating U Y Q

theorem IsSafe.isAlternating {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSafe Y Q) : IsAlternating Y Q :=
  h.1

theorem IsBracketSafe.isSafe {U Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsBracketSafe U Y Q) : IsSafe Y Q :=
  h.1

theorem IsBracketSafe.isBracketAlternating
    {U Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsBracketSafe U Y Q) : IsBracketAlternating U Y Q :=
  h.2

theorem IsBracketSafe.isAlternating
    {U Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsBracketSafe U Y Q) : IsAlternating Y Q :=
  h.1.1

theorem IsBracketSafe.reference_isWarp
    {U Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsBracketSafe U Y Q) : Γ.IsWarp Y :=
  h.1.1.1

/-- The exact universally quantified statement of source Lemma 4.9. -/
def SafeSwitchingStatement (Γ : DWeb V) : Prop :=
  ∀ (Y : Set Γ.DPath) (Q : AltPath Γ.graph),
    Γ.IsWarp Y → Γ.HasFiniteCharacter Y → IsSafe Y Q →
      (Cyclowarp.application Y Q).HasFiniteWarpRealization

/-- A reducing alternating path for a warp begins at one of its finite
terminals and ends at one of its initial vertices. -/
def IsReducing (Y : Set Γ.DPath) (Q : AltPath Γ.graph) : Prop :=
  IsAlternating Y Q ∧
    ∃ v ∈ Γ.terminalFrontier Y, Q.initial = v ∧
      ∃ u ∈ Γ.initialSet Y, Q.terminal? = some u

/-- A finite endpoint assignment, or the symbol `∞`. -/
inductive AltEnd (V : Type u)
  | vertex (v : V)
  | infinity
  deriving DecidableEq

/-- The endpoints of an alternating path agree with an `AltEnd`. -/
def HasEnd (Q : AltPath Γ.graph) : AltEnd V → Prop
  | .vertex v => Q.terminal? = some v
  | .infinity => Q.IsInfinite

/-- Degeneracy, Definition 4.10, expressed by existence of a resulting path
in the switched edge relation. -/
def IsDegenerate (Y : Set Γ.DPath) (Q : AltPath Γ.graph) (e : AltEnd V) : Prop :=
  match e with
  | .vertex v =>
      ∃ p : DirectedPath.FinitePath Γ.graph,
        p.start = Q.initial ∧ p.finish = v ∧
          (Cyclowarp.application Y Q).ContainsFinitePath p
  | .infinity =>
      ∃ r : DirectedPath.Ray Γ.graph,
        r.initial = Q.initial ∧ (Cyclowarp.application Y Q).ContainsRay r

/-! ## Source-faithful result interfaces -/

/-- A nontrivial finite-or-infinite directed path. -/
def PathNontrivial (p : Γ.DPath) : Prop :=
  ∃ x ∈ p.support, ∃ y ∈ p.support, x ≠ y

/-- The paper's fractured warps.  Their paths may touch only when the
terminal of one is the initial vertex of the other; nevertheless their edge
union must be the edge union of an honest warp. -/
structure FracturedWarp (Γ : DWeb V) where
  paths : Set Γ.DPath
  edgeWarp : Set Γ.DPath
  edgeWarp_isWarp : Γ.IsWarp edgeWarp
  same_edges : familyEdges paths = familyEdges edgeWarp
  allowed_intersection : ∀ ⦃p⦄, p ∈ paths → ∀ ⦃q⦄, q ∈ paths → p ≠ q →
    ¬ Disjoint p.support q.support →
      PathNontrivial p ∧ PathNontrivial q ∧
        ((∃ t, Γ.terminal? q = some t ∧ p.initial = t ∧
            p.support ∩ q.support = {t}) ∨
          (∃ t, Γ.terminal? p = some t ∧ q.initial = t ∧
            p.support ∩ q.support = {t}))

namespace FracturedWarp

theorem hasFiniteCharacter_of_subset {Z : FracturedWarp Γ}
    (hfin : Γ.HasFiniteCharacter Z.paths) {W : Set Γ.DPath}
    (hW : W ⊆ Z.paths) : Γ.HasFiniteCharacter W :=
  fun hp ↦ hfin (hW hp)

end FracturedWarp

/-- The alternatives in Lemma 4.13. -/
def SafeAlternatingDichotomy (Z Y : Set Γ.DPath) (u : V) : Prop :=
  (∃ Q : AltPath Γ.graph,
    IsBracketSafe Z Y Q ∧ Q.initial = u ∧ Q.IsInfinite) ∨
  (∃ v ∈ Γ.terminalFrontier Z \ Γ.vertexSet Y,
    ∃ Q : AltPath Γ.graph,
      IsBracketSafe Z Y Q ∧ Q.initial = u ∧ Q.terminal? = some v ∧
        ∃ T : AltPath Γ.graph,
          IsBracketAlternating Y Z T ∧ T.initial = v ∧ T.terminal? = some u)

/-- A local strengthening of the finite alternative whose reducing path can
be fed to the corrected exact switching lemma.  This proposition is useful
when a particular construction supplies the marks, but it is deliberately
*not* universally quantified: even for finite normalized endpoint-pure warps
the literal dichotomy need not admit a contact-marked reducing witness. -/
def ContactMarkedSafeAlternatingDichotomy
    (Z Y : Set Γ.DPath) (u : V) : Prop :=
  (∃ Q : AltPath Γ.graph,
    IsBracketSafe Z Y Q ∧ Q.initial = u ∧ Q.IsInfinite) ∨
  (∃ v ∈ Γ.terminalFrontier Z \ Γ.vertexSet Y,
    ∃ Q : AltPath Γ.graph,
      IsBracketSafe Z Y Q ∧ Q.initial = u ∧ Q.terminal? = some v ∧
        ∃ T : AltPath Γ.graph,
          IsBracketSwitchingAlternating Y Z T ∧
            T.initial = v ∧ T.terminal? = some u)

/-- Forgetting the contact marks on the reducing path gives the literal
source alternative. -/
theorem ContactMarkedSafeAlternatingDichotomy.toSafeAlternatingDichotomy
    {Z Y : Set Γ.DPath} {u : V}
    (h : ContactMarkedSafeAlternatingDichotomy Z Y u) :
    SafeAlternatingDichotomy Z Y u := by
  rcases h with h | h
  · exact Or.inl h
  · right
    rcases h with ⟨v, hv, Q, hQ, hQi, hQt, T, hT, hTi, hTt⟩
    exact ⟨v, hv, Q, hQ, hQi, hQt, T, hT.1, hTi, hTt⟩

/-- The literal universally quantified statement of source Lemma 4.13.
The published lemma is a statement about two finite-character warps; it does
not mention the source and target sides of the ambient web. -/
def SourceSafeAlternatingDichotomyStatement (Γ : DWeb V) : Prop :=
  ∀ (Z Y : Set Γ.DPath),
    Γ.IsWarp Z → Γ.IsWarp Y →
    Γ.HasFiniteCharacter Z → Γ.HasFiniteCharacter Y →
    Γ.initialSet Y ⊆ Γ.initialSet Z →
    ∀ u ∈ Γ.initialSet Z \ Γ.vertexSet Y,
      SafeAlternatingDichotomy Z Y u

/-- The normalized, endpoint-pure specialization of Lemma 4.13 used by the
simultaneous-assignment recursion.  Unlike
`SourceSafeAlternatingDichotomyStatement`, this packages the standing
Assumption 2.1 and the application-specific fact that `Z` runs from the
source side to the target side. -/
def SafeAlternatingDichotomyStatement (Γ : DWeb V) : Prop :=
  Γ.IsNormalized →
  ∀ (Z Y : Set Γ.DPath),
    Γ.initialSet Z ⊆ Γ.source →
    Γ.terminalFrontier Z ⊆ Γ.target →
    Γ.IsWarp Z → Γ.IsWarp Y →
    Γ.HasFiniteCharacter Z → Γ.HasFiniteCharacter Y →
    Γ.initialSet Y ⊆ Γ.initialSet Z →
    ∀ u ∈ Γ.initialSet Z \ Γ.vertexSet Y,
      SafeAlternatingDichotomy Z Y u

/-- The complete output of Theorem 4.12.  Its domain is exactly the sources
of `Z` not already used as sources by `Y`; finite assigned endpoints are
pairwise distinct.  The source theorem asks for `Y`-safe paths, not for the
stronger condition that every forward link remain a fragment of the original
`Z` after the successive switching steps. -/
structure SimultaneousAssignment (Z Y : Set Γ.DPath) where
  assigned : {z : V // z ∈ Γ.initialSet Z \ Γ.initialSet Y} → AltPath Γ.graph
  starts_at : ∀ z, (assigned z).initial = z.1
  safe : ∀ z, IsSafe Y (assigned z)
  leaving : ∀ z, IsLeaving Y (assigned z)
  maximal : ∀ z,
    (assigned z).IsInfinite ∨
      ∃ v ∈ Γ.terminalFrontier Z \ Γ.vertexSet Y,
        (assigned z).terminal? = some v
  finite_terminals_injective :
    ∀ ⦃z₁ z₂ v⦄,
      (assigned z₁).terminal? = some v →
      (assigned z₂).terminal? = some v → z₁ = z₂

namespace SimultaneousAssignment

/-- Theorem 4.12 has a canonical empty assignment when there are no
uncovered `Z`-sources. -/
def of_initialSet_subset {Z Y : Set Γ.DPath}
    (h : Γ.initialSet Z ⊆ Γ.initialSet Y) : SimultaneousAssignment Z Y where
  assigned z := False.elim (z.property.2 (h z.property.1))
  starts_at z := False.elim (z.property.2 (h z.property.1))
  safe z := False.elim (z.property.2 (h z.property.1))
  leaving z := False.elim (z.property.2 (h z.property.1))
  maximal z := False.elim (z.property.2 (h z.property.1))
  finite_terminals_injective := by
    intro z₁ z₂ v _ _
    exact False.elim (z₁.property.2 (h z₁.property.1))

theorem finite_terminal_mem {Z Y : Set Γ.DPath}
    (A : SimultaneousAssignment Z Y)
    (z : {z : V // z ∈ Γ.initialSet Z \ Γ.initialSet Y})
    {v : V} (hv : (A.assigned z).terminal? = some v) :
    v ∈ Γ.terminalFrontier Z \ Γ.vertexSet Y := by
  rcases A.maximal z with hinf | ⟨w, hw, hterm⟩
  · cases hQ : A.assigned z with
    | trivial x => simp [AltPath.IsInfinite, hQ] at hinf
    | finite Q => simp [AltPath.IsInfinite, hQ] at hinf
    | infinite Q => simp [AltPath.terminal?, hQ] at hv
  · have : v = w := by simpa [hv] using hterm
    exact this ▸ hw

end SimultaneousAssignment

/-- The literal universally quantified statement of source Theorem 4.12.
The theorem explicitly notes that the assigned alternating paths need not be
pairwise disjoint; only their finite terminals are distinct. -/
def SourceSimultaneousAssignmentStatement (Γ : DWeb V) : Prop :=
  ∀ (Z Y : Set Γ.DPath),
    Γ.IsWarp Z → Γ.IsWarp Y →
    Γ.HasFiniteCharacter Z → Γ.HasFiniteCharacter Y →
    Γ.initialSet Y ⊆ Γ.initialSet Z →
    Nonempty (SimultaneousAssignment Z Y)

/-- The normalized, endpoint-pure specialization of source Theorem 4.12
used in the web applications.  The extra hypotheses are deliberately visible
rather than being attributed to the literal statement of the theorem. -/
def SimultaneousAssignmentStatement (Γ : DWeb V) : Prop :=
  Γ.IsNormalized →
  ∀ (Z Y : Set Γ.DPath),
    Γ.initialSet Z ⊆ Γ.source →
    Γ.terminalFrontier Z ⊆ Γ.target →
    Γ.IsWarp Z → Γ.IsWarp Y →
    Γ.HasFiniteCharacter Z → Γ.HasFiniteCharacter Y →
    Γ.initialSet Y ⊆ Γ.initialSet Z →
    Nonempty (SimultaneousAssignment Z Y)

/-- Remark 4.20: the simultaneous-assignment conclusion remains valid for
a fractured first warp, after duplicating every shared terminal/initial
vertex and projecting the resulting alternating paths back. -/
def FracturedSimultaneousAssignmentStatement (Γ : DWeb V) : Prop :=
  Γ.IsNormalized →
  ∀ (Z : FracturedWarp Γ) (Y : Set Γ.DPath),
    Γ.initialSet Z.paths ⊆ Γ.source →
    Γ.terminalFrontier Z.paths ⊆ Γ.target →
    Γ.IsWarp Y →
    Γ.HasFiniteCharacter Z.paths → Γ.HasFiniteCharacter Y →
    Γ.initialSet Y ⊆ Γ.initialSet Z.paths →
    Nonempty (SimultaneousAssignment Z.paths Y)

end Alternating
end Erdos599
