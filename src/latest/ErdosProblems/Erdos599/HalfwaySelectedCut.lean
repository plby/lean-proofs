/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClosureFirstCutCore
import ErdosProblems.Erdos599.HalfwayFirstFragmentAudit
import ErdosProblems.Erdos599.FracturedAssignmentPeel
import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Contact-segmented assignments at the Section 9 closing set

Bracket provenance by itself does not prevent a projected alternating path
from leaving a set and later re-entering it on a backward reference link.
Consequently a whole assigned route cannot in general be compressed to one
imaginary edge.  A possible corrected transaction would have to split it at
its contacts with the closed set, submit safe outside-open pieces separately
to Claim 2, and retain directed realizations of the closed blocks in the old
reference/layer geometry.

The first part of this file gives a conditional API for such a transaction.
It records exact endpoint chaining, vertex/edge reconstruction, provenance
in the original assigned route, and the Claim-2 certificates of every
outside piece.  These certificates are not derivable from bracket safeness
and path closure alone: cutting at a covered contact can destroy safeness,
and a closed backward block is traversed opposite its graph orientation.
The explicit directed-realization record below isolates the additional
source construction which would be required.  This file deliberately does
not change the older one-edge downstream API.  The four-vertex model below
formally proves that the closure, boundary, and literal-hole facts stated at
the Claim 1/Claim 2 handoff do not construct these certificates: both the
first-hit prefix and last-exit suffix can fail safeness.

The final part retains a useful conditional lemma under the substantially
stronger hypothesis `ClosedUnderPaths Gamma W X`.  That lemma is not an
instance of Assertions 9.22--9.25: the later linkage `W` is constructed only
after the omega closure and is not the earlier slice-difference family.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y W closureFamily : Set Gamma.DPath}
variable {X before innerRoof outerRoof : Set V}

/-! ## The contact-segmented replacement for one-edge compression -/

/-- Link support is part of the vertex set of the ambient alternating
route.  This small bridge is intentionally independent of safeness. -/
theorem AltPath.mem_vertexSet_of_mem_link_support
    {Q : AltPath Gamma.graph} {l : Link Gamma.graph}
    (hl : l ∈ Q.links) {x : V} (hx : x ∈ l.path.support) :
    x ∈ Q.vertexSet := by
  cases Q with
  | trivial v => simp [AltPath.links] at hl
  | finite T =>
      rcases hl with ⟨i, rfl⟩
      exact Set.mem_iUnion.2 ⟨i, hx⟩
  | infinite T =>
      rcases hl with ⟨i, rfl⟩
      exact Set.mem_iUnion.2 ⟨i, hx⟩

/-- Last-exit truncation has the obstruction dual to the first-fragment
obstruction recorded in `HalfwayFirstFragmentAudit`: a one-link forward
path cannot be safe if its entry is already covered by the reference warp.
In particular, cutting a safe route immediately after its last visit to a
closed reference block does not in general leave a safe suffix. -/
theorem not_isSafe_single_forward_of_entry_mem_reference
    (l : Link Gamma.graph) (hforward : l.direction = .forward)
    (hentry : l.entry ∈ Gamma.vertexSet Y) :
    ¬ IsSafe Y (.finite (.singleton l)) := by
  intro hsafe
  have hfirst :
      (AltPath.finite (FiniteTrace.singleton l)).firstDirection? =
        some .forward := by
    change some l.direction = some .forward
    rw [hforward]
  exact (hsafe.isAlternating.2.2.1 hfirst) hentry

/-- What reference-path closure actually says about a contacted backward
link.  It turns the *whole* backward fragment into a closed block; it does
not prevent the route from traversing that block and later leaving `X` on a
new forward link.  This is the precise reason Claim 1(3) of Assertion 9.31
does not by itself imply endpoint-cleanliness of the assigned SAP. -/
theorem backward_link_support_subset_of_closedUnderPaths
    {Q : AltPath Gamma.graph}
    (hclosed : ClosedUnderPaths Gamma Y X)
    (hQ : IsBracketSafe W Y Q)
    {l : Link Gamma.graph} (hl : l ∈ Q.links)
    (hbackward : l.direction = .backward)
    (hcontact : (l.path.support ∩ X).Nonempty) :
    l.path.support ⊆ X := by
  rcases hQ.isAlternating.2.1 l hl hbackward with ⟨p, hpY, hlp⟩
  rcases hcontact with ⟨x, hxl, hxX⟩
  exact hlp.1.trans (hclosed p hpY ⟨x, hlp.1 hxl, hxX⟩)

/-! ### A checked endpoint-cleanliness obstruction

The following four-vertex configuration is the minimal obstruction hidden by
the prose transition from Claim 1 to Claim 2 in Assertion 9.31.  The two
forward paths are literal holes of a cut warp, and the backward path is one
whole reference component contained in the closing set. -/

namespace EndpointCleanCounterexample

inductive Vertex
  | s | a | b | t
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj x y := (x = s ∧ y = a) ∨ (x = b ∧ y = a) ∨
    (x = b ∧ y = t)

@[simp] theorem graph_adj (x y : Vertex) :
    graph.Adj x y ↔
      (x = s ∧ y = a) ∨ (x = b ∧ y = a) ∨
        (x = b ∧ y = t) :=
  Iff.rfl

def sa : FinitePath graph where
  start := s
  finish := a
  walk := Walk.cons (u := s) (v := a) (w := a) (by simp [graph]) Walk.nil
  isPath := by
    change [s, a].Nodup
    simp

def ba : FinitePath graph where
  start := b
  finish := a
  walk := Walk.cons (u := b) (v := a) (w := a) (by simp [graph]) Walk.nil
  isPath := by
    change [b, a].Nodup
    simp

def bt : FinitePath graph where
  start := b
  finish := t
  walk := Walk.cons (u := b) (v := t) (w := t) (by simp [graph]) Walk.nil
  isPath := by
    change [b, t].Nodup
    simp

@[simp] theorem support_sa : sa.support = {s, a} := by
  ext x
  change x ∈ [s, a] ↔ _
  simp

@[simp] theorem support_ba : ba.support = {b, a} := by
  ext x
  change x ∈ [b, a] ↔ _
  simp

@[simp] theorem support_bt : bt.support = {b, t} := by
  ext x
  change x ∈ [b, t] ↔ _
  simp

def web : DWeb Vertex where
  graph := graph
  source := {s, b}
  target := {a, t}

def holes : Set web.DPath := {Sum.inl sa, Sum.inl bt}
def reference : Set web.DPath := {Sum.inl ba}
def cut : Set Vertex := {a, b}

private theorem sa_mem_holes : (Sum.inl sa : web.DPath) ∈ holes := by
  change Sum.inl sa = Sum.inl sa ∨ Sum.inl sa = Sum.inl bt
  exact Or.inl rfl

private theorem bt_mem_holes : (Sum.inl bt : web.DPath) ∈ holes := by
  change Sum.inl bt = Sum.inl sa ∨ Sum.inl bt = Sum.inl bt
  exact Or.inr rfl

private theorem ba_mem_reference : (Sum.inl ba : web.DPath) ∈ reference := by
  change Sum.inl ba = Sum.inl ba
  rfl

@[simp] private theorem path_support_sa :
    DirectedPath.Path.support (Sum.inl sa : web.DPath) = {s, a} :=
  support_sa

@[simp] private theorem path_support_ba :
    DirectedPath.Path.support (Sum.inl ba : web.DPath) = {b, a} :=
  support_ba

@[simp] private theorem path_support_bt :
    DirectedPath.Path.support (Sum.inl bt : web.DPath) = {b, t} :=
  support_bt

theorem holes_isWarp : web.IsWarp holes := by
  intro p hp q hq hpq
  change p = Sum.inl sa ∨ p = Sum.inl bt at hp
  change q = Sum.inl sa ∨ q = Sum.inl bt at hq
  rcases hp with rfl | rfl
  · rcases hq with rfl | rfl
    · exact (hpq rfl).elim
    · change Disjoint sa.support bt.support
      rw [support_sa, support_bt]
      simp [Set.disjoint_left]
  · rcases hq with rfl | rfl
    · change Disjoint bt.support sa.support
      rw [support_bt, support_sa]
      simp [Set.disjoint_left]
    · exact (hpq rfl).elim

theorem holes_finite : web.HasFiniteCharacter holes := by
  intro p hp
  change p = Sum.inl sa ∨ p = Sum.inl bt at hp
  rcases hp with rfl | rfl
  · exact ⟨sa, rfl⟩
  · exact ⟨bt, rfl⟩

theorem reference_isWarp : web.IsWarp reference := by
  intro p hp q hq hpq
  change p = Sum.inl ba at hp
  change q = Sum.inl ba at hq
  exact (hpq (hp.trans hq.symm)).elim

theorem reference_finite : web.HasFiniteCharacter reference := by
  intro p hp
  change p = Sum.inl ba at hp
  subst p
  exact ⟨ba, rfl⟩

/-- Claim 1(3) holds: the sole reference path which meets the cut is wholly
contained in it. -/
theorem reference_closed : ClosedUnderPaths web reference cut := by
  intro p hp _hmeet
  change p = Sum.inl ba at hp
  subst p
  intro x hx
  change x ∈ ba.support at hx
  rw [support_ba] at hx
  rcases hx with rfl | rfl <;> simp [cut]

/-- Each literal hole meets the cut only at one displayed endpoint. -/
theorem hole_cut_vertex_is_endpoint
    (p : web.DPath) (hp : p ∈ holes) {x : Vertex}
    (hxp : x ∈ p.support) (hxcut : x ∈ cut) :
    p.initial = x ∨ web.terminal? p = some x := by
  change p = Sum.inl sa ∨ p = Sum.inl bt at hp
  rcases hp with rfl | rfl
  · change sa.start = x ∨ some sa.finish = some x
    change x ∈ sa.support at hxp
    rw [support_sa] at hxp
    simp only [cut, Set.mem_insert_iff, Set.mem_singleton_iff] at hxcut
    rcases hxp with (rfl | rfl) <;> simp_all [sa]
  · change bt.start = x ∨ some bt.finish = some x
    change x ∈ bt.support at hxp
    rw [support_bt] at hxp
    simp only [cut, Set.mem_insert_iff, Set.mem_singleton_iff] at hxcut
    rcases hxp with (rfl | rfl) <;> simp_all [bt]

theorem s_initial_holes : s ∈ web.initialSet holes :=
  ⟨Sum.inl sa, sa_mem_holes, rfl⟩

theorem b_initial_holes : b ∈ web.initialSet holes :=
  ⟨Sum.inl bt, bt_mem_holes, rfl⟩

theorem b_initial_reference : b ∈ web.initialSet reference :=
  ⟨Sum.inl ba, ba_mem_reference, rfl⟩

theorem a_terminal_holes : a ∈ web.terminalFrontier holes :=
  ⟨Sum.inl sa, sa_mem_holes, rfl⟩

theorem t_terminal_holes : t ∈ web.terminalFrontier holes :=
  ⟨Sum.inl bt, bt_mem_holes, rfl⟩

theorem a_terminal_reference : a ∈ web.terminalFrontier reference :=
  ⟨Sum.inl ba, ba_mem_reference, rfl⟩

theorem s_not_vertex_reference : s ∉ web.vertexSet reference := by
  rintro ⟨p, hp, hs⟩
  change p = Sum.inl ba at hp
  subst p
  change s ∈ ba.support at hs
  rw [support_ba] at hs
  simp at hs

theorem t_not_vertex_reference : t ∉ web.vertexSet reference := by
  rintro ⟨p, hp, ht⟩
  change p = Sum.inl ba at hp
  subst p
  change t ∈ ba.support at ht
  rw [support_ba] at ht
  simp at ht

theorem reference_initials_subset_holes :
    web.initialSet reference ⊆ web.initialSet holes := by
  rintro x ⟨p, hp, hpx⟩
  change p = Sum.inl ba at hp
  subst p
  change ba.start = x at hpx
  rw [← hpx]
  exact b_initial_holes

/-- The same initial/terminal boundary alignment used by Remark 4.20 holds
in the obstruction. -/
theorem boundaryAligned : BoundaryAligned holes reference := by
  constructor
  · rintro x ⟨⟨p, hp, hpx⟩, hxRef⟩
    change p = Sum.inl sa ∨ p = Sum.inl bt at hp
    rcases hp with rfl | rfl
    · change sa.start = x at hpx
      subst x
      exact (s_not_vertex_reference hxRef).elim
    · change bt.start = x at hpx
      subst x
      exact b_initial_reference
  · rintro x ⟨⟨p, hp, hpx⟩, hxRef⟩
    change p = Sum.inl sa ∨ p = Sum.inl bt at hp
    rcases hp with rfl | rfl
    · change some sa.finish = some x at hpx
      have hxa : x = a := Option.some.inj hpx.symm
      subst x
      exact a_terminal_reference
    · change some bt.finish = some x at hpx
      have hxt : x = t := Option.some.inj hpx.symm
      subst x
      exact (t_not_vertex_reference hxRef).elim

/-- Here the literal holes are already disjoint, hence form a particularly
simple fractured warp with themselves as recombination. -/
def fractured : FracturedWarp web where
  paths := holes
  edgeWarp := holes
  edgeWarp_isWarp := holes_isWarp
  same_edges := rfl
  allowed_intersection := by
    intro p hp q hq hpq hmeet
    exact (hmeet (holes_isWarp hp hq hpq)).elim

def first : Link graph where
  path := sa
  direction := .forward
  nontrivial := by simp [sa]

def bridge : Link graph where
  path := ba
  direction := .backward
  nontrivial := by simp [ba]

def last : Link graph where
  path := bt
  direction := .forward
  nontrivial := by simp [bt]

private theorem compatible_first_bridge (P : Prop) (hP : P) :
    CompatibleInOrder P first bridge := by
  simp only [CompatibleInOrder, first, bridge]
  constructor
  · intro _
    change sa.support ∩ ba.support = {a}
    rw [support_sa, support_ba]
    ext x
    cases x <;> simp
  · intro hn
    exact (hn hP).elim

private theorem compatible_bridge_last (P : Prop) (hP : P) :
    CompatibleInOrder P bridge last := by
  simp only [CompatibleInOrder, bridge, last]
  constructor
  · intro _ v hvba hvbt
    rw [support_ba] at hvba
    rw [support_bt] at hvbt
    left
    change v = b
    rcases hvba with rfl | rfl <;> simp_all
  · intro hn
    exact (hn hP).elim

private theorem compatible_first_last (P : Prop) :
    CompatibleInOrder P first last := by
  simp [CompatibleInOrder, first, last, Link.exit, Link.entry]

private def traceLink (i : Fin 3) : Link graph :=
  if i.1 = 0 then first else if i.1 = 1 then bridge else last

@[simp] private theorem traceLink_zero : traceLink 0 = first := by
  simp [traceLink]

@[simp] private theorem traceLink_one : traceLink 1 = bridge := by
  simp [traceLink]

@[simp] private theorem traceLink_two : traceLink 2 = last := by
  simp [traceLink]

def trace : FiniteTrace graph where
  lastIndex := 2
  link := traceLink
  joins := by
    intro i
    have hi : i.1 = 0 ∨ i.1 = 1 := by omega
    rcases hi with hi | hi
    · have hieq : i = (0 : Fin 2) := Fin.ext hi
      subst i
      rfl
    · have hieq : i = (1 : Fin 2) := Fin.ext hi
      subst i
      rfl
  alternates := by
    intro i
    have hi : i.1 = 0 ∨ i.1 = 1 := by omega
    rcases hi with hi | hi
    · have hieq : i = (0 : Fin 2) := Fin.ext hi
      subst i
      simp [traceLink, first, bridge]
    · have hieq : i = (1 : Fin 2) := Fin.ext hi
      subst i
      simp [traceLink, bridge, last]
  compatible := by
    intro i j hij
    have hpairs :
        (i.1 = 0 ∧ j.1 = 1) ∨ (i.1 = 0 ∧ j.1 = 2) ∨
          (i.1 = 1 ∧ j.1 = 2) := by omega
    rcases hpairs with hp | hp | hp
    · have hi : i = (0 : Fin 3) := Fin.ext hp.1
      have hj : j = (1 : Fin 3) := Fin.ext hp.2
      subst i
      subst j
      simp only [traceLink_zero, traceLink_one]
      exact compatible_first_bridge _ (by omega)
    · have hi : i = (0 : Fin 3) := Fin.ext hp.1
      have hj : j = (2 : Fin 3) := Fin.ext hp.2
      subst i
      subst j
      simp only [traceLink_zero, traceLink_two]
      exact compatible_first_last _
    · have hi : i = (1 : Fin 3) := Fin.ext hp.1
      have hj : j = (2 : Fin 3) := Fin.ext hp.2
      subst i
      subst j
      simp only [traceLink_one, traceLink_two]
      exact compatible_bridge_last _ (by omega)

def route : AltPath web.graph := .finite trace

@[simp] theorem route_initial : route.initial = s := rfl
@[simp] theorem route_terminal : route.terminal? = some t := rfl

private theorem mem_route_links_iff {l : Link web.graph} :
    l ∈ route.links ↔ l = first ∨ l = bridge ∨ l = last := by
  constructor
  · rintro ⟨i, rfl⟩
    change Fin 3 at i
    have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by omega
    rcases hi with hi | hi | hi
    · have hieq : i = (0 : Fin 3) := Fin.ext hi
      subst i
      exact Or.inl rfl
    · have hieq : i = (1 : Fin 3) := Fin.ext hi
      subst i
      exact Or.inr (Or.inl rfl)
    · have hieq : i = (2 : Fin 3) := Fin.ext hi
      subst i
      exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨(0 : Fin 3), rfl⟩
    · exact ⟨(1 : Fin 3), rfl⟩
    · exact ⟨(2 : Fin 3), rfl⟩

theorem route_isBracketAlternating :
    IsBracketAlternating holes reference route := by
  constructor
  · refine ⟨reference_isWarp, ?_, ?_, ?_⟩
    · intro l hl hback
      rw [mem_route_links_iff] at hl
      rcases hl with rfl | rfl | rfl
      · simp [first] at hback
      · exact ⟨Sum.inl ba, ba_mem_reference, ba.isSubpathOf_self⟩
      · simp [last] at hback
    · intro _hfirst
      rintro ⟨p, hp, hs⟩
      have hp' : p = Sum.inl ba := hp
      subst p
      change s ∈ ba.support at hs
      rw [support_ba] at hs
      simp at hs
    · intro x hterminal _hlast
      have hxt : x = t :=
        Option.some.inj (hterminal.symm.trans route_terminal)
      subst x
      rintro ⟨p, hp, ht⟩
      have hp' : p = Sum.inl ba := hp
      subst p
      change t ∈ ba.support at ht
      rw [support_ba] at ht
      simp at ht
  · intro l hl hforward
    rw [mem_route_links_iff] at hl
    rcases hl with rfl | rfl | rfl
    · exact ⟨Sum.inl sa, sa_mem_holes, sa.isSubpathOf_self⟩
    · simp [bridge] at hforward
    · exact ⟨Sum.inl bt, bt_mem_holes, bt.isSubpathOf_self⟩

private theorem route_backwardEdges :
    route.directionEdges .backward = ba.edgeSet := by
  ext e
  simp only [AltPath.directionEdges, Set.mem_iUnion]
  constructor
  · rintro ⟨l, hl, hback, he⟩
    rw [mem_route_links_iff] at hl
    rcases hl with rfl | rfl | rfl
    · simp [first] at hback
    · exact he
    · simp [last] at hback
  · intro he
    exact ⟨bridge, (mem_route_links_iff.mpr (Or.inr (Or.inl rfl))), rfl, he⟩

/-- The bad route is nevertheless a genuine safe `[holes,reference]` SAP. -/
theorem route_isBracketSafe : IsBracketSafe holes reference route := by
  apply isBracketSafe_of_intervals holes_isWarp holes_finite
    route_isBracketAlternating
  intro p hp
  have hp' : p = Sum.inl ba := hp
  subst p
  rw [route_backwardEdges]
  exact fragment_inter_isEdgeInterval reference_isWarp ba
    ⟨Sum.inl ba, ba_mem_reference, ba.isSubpathOf_self⟩
    (Sum.inl ba) ba_mem_reference

theorem a_vertex_reference : a ∈ web.vertexSet reference :=
  ⟨Sum.inl ba, ba_mem_reference, by
    change a ∈ ba.support
    rw [support_ba]
    simp⟩

theorem b_vertex_reference : b ∈ web.vertexSet reference :=
  ⟨Sum.inl ba, ba_mem_reference, by
    change b ∈ ba.support
    rw [support_ba]
    simp⟩

/-- First-hit truncation fails at the covered terminal `a`. -/
theorem first_fragment_not_safe :
    ¬ IsSafe reference (.finite (.singleton first)) := by
  exact not_isSafe_single_forward_of_exit_mem_reference
    (Gamma := web) (Y := reference) first rfl
      (by
        change a ∈ web.vertexSet reference
        exact a_vertex_reference)

/-- Last-exit truncation fails symmetrically at the covered initial `b`. -/
theorem last_fragment_not_safe :
    ¬ IsSafe reference (.finite (.singleton last)) := by
  exact not_isSafe_single_forward_of_entry_mem_reference
    (Gamma := web) (Y := reference) last rfl
      (by
        change b ∈ web.vertexSet reference
        exact b_vertex_reference)

/-- The two internal contacts are not the displayed endpoints.  This is the
negation of the missing premise used when Claim 2 is invoked in 9.31. -/
theorem route_not_endpoint_clean :
    ¬ (route.vertexSet ∩ cut ⊆ {s, t}) := by
  intro hclean
  have haRoute : a ∈ route.vertexSet := by
    apply AltPath.mem_vertexSet_of_mem_link_support
      (Q := route) (l := first)
    · exact mem_route_links_iff.mpr (Or.inl rfl)
    · change a ∈ sa.support
      rw [support_sa]
      simp
  have haEnd := hclean ⟨haRoute, by simp [cut]⟩
  simp at haEnd

/-- A compact formal refutation of the tempting missing lemma.  All local
hypotheses available at the Claim 1/Claim 2 handoff hold simultaneously,
but endpoint-cleanliness fails. -/
theorem closure_and_literal_cut_do_not_force_endpoint_clean :
    web.IsWarp holes ∧ web.HasFiniteCharacter holes ∧
      web.IsWarp reference ∧ web.HasFiniteCharacter reference ∧
      BoundaryAligned holes reference ∧
      web.initialSet reference ⊆ web.initialSet holes ∧
      ClosedUnderPaths web reference cut ∧
      (∀ p ∈ holes, ∀ x ∈ p.support, x ∈ cut →
        p.initial = x ∨ web.terminal? p = some x) ∧
      IsBracketSafe holes reference route ∧
      route.initial = s ∧ route.terminal? = some t ∧
      ¬ (route.vertexSet ∩ cut ⊆ {s, t}) := by
  exact ⟨holes_isWarp, holes_finite, reference_isWarp, reference_finite,
    boundaryAligned, reference_initials_subset_holes, reference_closed,
    hole_cut_vertex_is_endpoint, route_isBracketSafe, route_initial,
    route_terminal, route_not_endpoint_clean⟩

end EndpointCleanCounterexample

/-- One finite outside-open segment of an assigned alternating route.  The
last five fields are exactly the inputs of Claim 2; the final two fields say
that this is genuinely a segment of the original assigned route. -/
structure Claim2ReadyFiniteSegment
    (Q : AltPath Gamma.graph) (X before innerRoof outerRoof : Set V)
    (u v : V) where
  path : AltPath Gamma.graph
  safe : IsSafe Y path
  starts_at : path.initial = u
  ends_at : path.terminal? = some v
  eligible : HammockEligible before innerRoof outerRoof u (.vertex v)
  interior_disjoint :
    Disjoint (hammockInterior u (.vertex v) path) X
  outside : ¬ path.vertexSet ⊆ X
  vertexSet_subset_original : path.vertexSet ⊆ Q.vertexSet
  edgeSet_subset_original : path.edgeSet ⊆ Q.edgeSet

namespace Claim2ReadyFiniteSegment

variable {Q : AltPath Gamma.graph} {u v : V}

/-- A finite outside-open segment is immediately classifiable by Claim 2. -/
theorem isImaginaryEdge
    (S : Claim2ReadyFiniteSegment (Y := Y) Q X before innerRoof outerRoof u v)
    {kappa : Cardinal.{u}}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    IsImaginaryEdge Gamma Y kappa u v :=
  isImaginaryEdge_of_closed hclosed S.eligible S.safe S.starts_at
    S.ends_at S.interior_disjoint S.outside

end Claim2ReadyFiniteSegment

/-- An infinite outside-open tail.  This is the terminal piece when an
infinite assigned route has only finitely many contacts with `X`. -/
structure Claim2ReadyInfiniteSegment
    (Q : AltPath Gamma.graph) (X before innerRoof outerRoof : Set V)
    (u : V) where
  path : AltPath Gamma.graph
  safe : IsSafe Y path
  starts_at : path.initial = u
  infinite : path.IsInfinite
  eligible : HammockEligible before innerRoof outerRoof u .infinity
  interior_disjoint : Disjoint (hammockInterior u .infinity path) X
  outside : ¬ path.vertexSet ⊆ X
  vertexSet_subset_original : path.vertexSet ⊆ Q.vertexSet
  edgeSet_subset_original : path.edgeSet ⊆ Q.edgeSet

namespace Claim2ReadyInfiniteSegment

variable {Q : AltPath Gamma.graph} {u : V}

/-- An infinite outside-open tail makes its first contact popular. -/
theorem isPopular
    (S : Claim2ReadyInfiniteSegment (Y := Y) Q X before innerRoof outerRoof u)
    {persistent : Set V} {kappa : Cardinal.{u}}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    IsPopular Gamma Y persistent kappa u :=
  isPopular_of_closed_infinite hclosed S.eligible S.safe S.starts_at
    S.infinite S.interior_disjoint S.outside

end Claim2ReadyInfiniteSegment

/-- A maximal closed block between two consecutive outside-open pieces.
This is provenance bookkeeping, not yet a directed realization: a backward
link is traversed opposite its ambient edge orientation.  Backward links
come from the reference warp and forward links, if any, come from the earlier
slice/layer family which was included in the omega closure. -/
structure ClosedContactBlock
    (Q : AltPath Gamma.graph) (X : Set V)
    (closureFamily : Set Gamma.DPath) (u v : V) where
  path : AltPath Gamma.graph
  starts_at : path.initial = u
  ends_at : path.terminal? = some v
  contained : path.vertexSet ⊆ X
  alternating : IsBracketAlternating closureFamily Y path
  vertexSet_subset_original : path.vertexSet ⊆ Q.vertexSet
  edgeSet_subset_original : path.edgeSet ⊆ Q.edgeSet

namespace ClosedContactBlock

variable {Q : AltPath Gamma.graph} {u v : V}

/-- A closed block uses only the two closed families and every endpoint of
each of its edges lies in `X`. -/
theorem edgeSet_subset_closedGeometry
    (B : ClosedContactBlock (Y := Y) Q X closureFamily u v) :
    B.path.edgeSet ⊆
      (familyEdges Y ∪ familyEdges closureFamily) ∩ (X ×ˢ X) := by
  intro e he
  refine ⟨B.path.edgeSet_subset_familyEdges_union_of_isBracketAlternating
    B.alternating he, ?_⟩
  rw [B.path.edgeSet_eq_iUnion_links] at he
  simp only [Set.mem_iUnion] at he
  obtain ⟨l, hl, hel⟩ := he
  have hend := l.path.edgeSet_subset_support_prod hel
  exact ⟨B.contained (AltPath.mem_vertexSet_of_mem_link_support hl hend.1),
    B.contained (AltPath.mem_vertexSet_of_mem_link_support hl hend.2)⟩

end ClosedContactBlock

namespace ClosedContactBlock

variable {Q : AltPath Gamma.graph} {u v : V}

/-- The genuinely missing bridge for a closed block: a directed path from
its traversal entry to its traversal exit in a proposed retained relation.
Neither `contained` nor `alternating` constructs this path, because backward
links have the wrong ambient orientation. -/
structure DirectedRealization
    (B : ClosedContactBlock (Y := Y) Q X closureFamily u v)
    (E : Set (V × V)) where
  path : FinitePath Gamma.graph
  starts_at : path.start = u
  ends_at : path.finish = v
  contained : path.support ⊆ X
  edges : path.edgeSet ⊆ E

end ClosedContactBlock

/-- A finite interval between consecutive recorded contacts. -/
inductive ContactPiece
    (Q : AltPath Gamma.graph) (X before innerRoof outerRoof : Set V)
    (closureFamily : Set Gamma.DPath) (u v : V)
  | outside :
      Claim2ReadyFiniteSegment (Y := Y) Q X before innerRoof outerRoof u v →
      ContactPiece Q X before innerRoof outerRoof closureFamily u v
  | closed : ClosedContactBlock (Y := Y) Q X closureFamily u v →
      ContactPiece Q X before innerRoof outerRoof closureFamily u v

namespace ContactPiece

variable {Q : AltPath Gamma.graph} {u v : V}

def path
    (P : ContactPiece (Y := Y) Q X before innerRoof outerRoof
      closureFamily u v) : AltPath Gamma.graph :=
  match P with
  | .outside S => S.path
  | .closed S => S.path

@[simp] theorem path_outside
    (S : Claim2ReadyFiniteSegment (Y := Y) Q X before innerRoof outerRoof u v) :
    (ContactPiece.outside (closureFamily := closureFamily) S).path = S.path := rfl

@[simp] theorem path_closed
    (S : ClosedContactBlock (Y := Y) Q X closureFamily u v) :
    (ContactPiece.closed (before := before) (innerRoof := innerRoof)
      (outerRoof := outerRoof) S).path = S.path := rfl

theorem starts_at
    (P : ContactPiece (Y := Y) Q X before innerRoof outerRoof
      closureFamily u v) : P.path.initial = u := by
  cases P with
  | outside S => exact S.starts_at
  | closed S => exact S.starts_at

theorem ends_at
    (P : ContactPiece (Y := Y) Q X before innerRoof outerRoof
      closureFamily u v) : P.path.terminal? = some v := by
  cases P with
  | outside S => exact S.ends_at
  | closed S => exact S.ends_at

theorem vertexSet_subset_original
    (P : ContactPiece (Y := Y) Q X before innerRoof outerRoof
      closureFamily u v) : P.path.vertexSet ⊆ Q.vertexSet := by
  cases P with
  | outside S => exact S.vertexSet_subset_original
  | closed S => exact S.vertexSet_subset_original

theorem edgeSet_subset_original
    (P : ContactPiece (Y := Y) Q X before innerRoof outerRoof
      closureFamily u v) : P.path.edgeSet ⊆ Q.edgeSet := by
  cases P with
  | outside S => exact S.edgeSet_subset_original
  | closed S => exact S.edgeSet_subset_original

end ContactPiece

/-- Exact finite contact decomposition of a finite assigned route.  The
points are ordered in traversal order, pieces share their displayed endpoint
definitionally, and `vertexSet_exact`/`edgeSet_exact` state that no part of
the original route was lost. -/
structure FiniteContactSegmentation
    (Q : AltPath Gamma.graph) (X before innerRoof outerRoof : Set V)
    (closureFamily : Set Gamma.DPath) where
  count : ℕ
  point : Fin (count + 1) → V
  point_injective : Function.Injective point
  piece : (i : Fin count) →
    ContactPiece (Y := Y) Q X before innerRoof outerRoof closureFamily
      (point i.castSucc) (point i.succ)
  initial_eq : point ⟨0, Nat.zero_lt_succ _⟩ = Q.initial
  terminal_eq : Q.terminal? =
    some (point ⟨count, Nat.lt_succ_self _⟩)
  internal_contact : ∀ i : Fin (count + 1),
    0 < i.1 → i.1 < count → point i ∈ X
  vertexSet_exact : Q.vertexSet =
    Set.range point ∪ ⋃ i, (piece i).path.vertexSet
  edgeSet_exact : Q.edgeSet = ⋃ i, (piece i).path.edgeSet

namespace FiniteContactSegmentation

variable {Q : AltPath Gamma.graph}

/-- Compress only the outside-open pieces.  Closed blocks are deliberately
absent from this relation and remain available through `piece`. -/
def compressedOutsideEdges
    (S : FiniteContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) : Set (V × V) :=
  {e | ∃ i T, S.piece i = ContactPiece.outside T ∧
    e = (S.point i.castSucc, S.point i.succ)}

theorem compressedOutsideEdges_subset_imaginaryGraph
    (S : FiniteContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily)
    {kappa : Cardinal.{u}}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    S.compressedOutsideEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  rintro e ⟨i, T, hi, rfl⟩
  have hT := T.isImaginaryEdge hclosed
  exact Or.inr hT

/-- Every edge retained in a closed block is an edge of the original
assigned route. -/
theorem closedPieceEdges_subset_original
    (S : FiniteContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) :
    (⋃ i, match S.piece i with
      | .outside _ => (∅ : Set (V × V))
      | .closed B => B.path.edgeSet) ⊆ Q.edgeSet := by
  intro e he
  simp only [Set.mem_iUnion] at he
  obtain ⟨i, hi⟩ := he
  cases hpiece : S.piece i with
  | outside T => simp [hpiece] at hi
  | closed B =>
      exact B.edgeSet_subset_original (by simpa [hpiece] using hi)

/-- A proposed directed relation realizes every closed interval in its
traversal orientation. -/
def ClosedBlocksRealizedBy
    (S : FiniteContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) (E : Set (V × V)) : Prop :=
  ∀ (i : Fin S.count) B, S.piece i = ContactPiece.closed B →
    Nonempty (B.DirectedRealization E)

end FiniteContactSegmentation

/-- Exact decomposition of an infinite assigned route with finitely many
closed-set contacts: a finite contact chain followed by one outside-open
infinite tail. -/
structure EventuallyOutsideSegmentation
    (Q : AltPath Gamma.graph) (X before innerRoof outerRoof : Set V)
    (closureFamily : Set Gamma.DPath) where
  count : ℕ
  point : Fin (count + 1) → V
  point_injective : Function.Injective point
  piece : (i : Fin count) →
    ContactPiece (Y := Y) Q X before innerRoof outerRoof closureFamily
      (point i.castSucc) (point i.succ)
  tail : Claim2ReadyInfiniteSegment (Y := Y) Q X before innerRoof outerRoof
    (point ⟨count, Nat.lt_succ_self _⟩)
  original_infinite : Q.IsInfinite
  initial_eq : point ⟨0, Nat.zero_lt_succ _⟩ = Q.initial
  internal_contact : ∀ i : Fin (count + 1), 0 < i.1 → point i ∈ X
  vertexSet_exact : Q.vertexSet =
    Set.range point ∪ (⋃ i, (piece i).path.vertexSet) ∪ tail.path.vertexSet
  edgeSet_exact : Q.edgeSet =
    (⋃ i, (piece i).path.edgeSet) ∪ tail.path.edgeSet

namespace EventuallyOutsideSegmentation

variable {Q : AltPath Gamma.graph}

def compressedOutsideEdges
    (S : EventuallyOutsideSegmentation (Y := Y) Q X before innerRoof
      outerRoof closureFamily) : Set (V × V) :=
  {e | ∃ i T, S.piece i = ContactPiece.outside T ∧
    e = (S.point i.castSucc, S.point i.succ)}

theorem compressedOutsideEdges_subset_imaginaryGraph
    (S : EventuallyOutsideSegmentation (Y := Y) Q X before innerRoof
      outerRoof closureFamily)
    {kappa : Cardinal.{u}}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    S.compressedOutsideEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  rintro e ⟨i, T, hi, rfl⟩
  exact Or.inr (T.isImaginaryEdge hclosed)

theorem tail_isPopular
    (S : EventuallyOutsideSegmentation (Y := Y) Q X before innerRoof
      outerRoof closureFamily)
    {persistent : Set V} {kappa : Cardinal.{u}}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    IsPopular Gamma Y persistent kappa
      (S.point ⟨S.count, Nat.lt_succ_self _⟩) :=
  S.tail.isPopular hclosed

def ClosedBlocksRealizedBy
    (S : EventuallyOutsideSegmentation (Y := Y) Q X before innerRoof
      outerRoof closureFamily) (E : Set (V × V)) : Prop :=
  ∀ (i : Fin S.count) B, S.piece i = ContactPiece.closed B →
    Nonempty (B.DirectedRealization E)

end EventuallyOutsideSegmentation

/-- Exact decomposition of an infinite route which has infinitely many
closed-set contacts. -/
structure OmegaContactSegmentation
    (Q : AltPath Gamma.graph) (X before innerRoof outerRoof : Set V)
  (closureFamily : Set Gamma.DPath) where
  point : ℕ → V
  point_injective : Function.Injective point
  piece : (i : ℕ) →
    ContactPiece (Y := Y) Q X before innerRoof outerRoof closureFamily
      (point i) (point (i + 1))
  original_infinite : Q.IsInfinite
  initial_eq : point 0 = Q.initial
  later_contact : ∀ i, point (i + 1) ∈ X
  vertexSet_exact : Q.vertexSet =
    Set.range point ∪ ⋃ i, (piece i).path.vertexSet
  edgeSet_exact : Q.edgeSet = ⋃ i, (piece i).path.edgeSet

namespace OmegaContactSegmentation

variable {Q : AltPath Gamma.graph}

def compressedOutsideEdges
    (S : OmegaContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) : Set (V × V) :=
  {e | ∃ i T, S.piece i = ContactPiece.outside T ∧
    e = (S.point i, S.point (i + 1))}

theorem compressedOutsideEdges_subset_imaginaryGraph
    (S : OmegaContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily)
    {kappa : Cardinal.{u}}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    S.compressedOutsideEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  rintro e ⟨i, T, hi, rfl⟩
  exact Or.inr (T.isImaginaryEdge hclosed)

def ClosedBlocksRealizedBy
    (S : OmegaContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) (E : Set (V × V)) : Prop :=
  ∀ (i : ℕ) B, S.piece i = ContactPiece.closed B →
    Nonempty (B.DirectedRealization E)

end OmegaContactSegmentation

/-- Finite, eventually-outside infinite, and infinitely-contacting routes
are the three possible outputs of the contact splitter. -/
inductive ContactSegmentation
    (Q : AltPath Gamma.graph) (X before innerRoof outerRoof : Set V)
    (closureFamily : Set Gamma.DPath)
  | finite : FiniteContactSegmentation (Y := Y) Q X before innerRoof
      outerRoof closureFamily → ContactSegmentation Q X before innerRoof
        outerRoof closureFamily
  | eventuallyOutside : EventuallyOutsideSegmentation (Y := Y) Q X before
      innerRoof outerRoof closureFamily → ContactSegmentation Q X before
        innerRoof outerRoof closureFamily
  | omega : OmegaContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily → ContactSegmentation Q X before innerRoof outerRoof
        closureFamily

namespace ContactSegmentation

variable {Q : AltPath Gamma.graph}

/-- A subrelation of an injectively indexed chain is bi-unique. -/
private theorem indexedEdges_biUnique
    {I J : Type*} {point : J → V} {source target : I → J}
    {E : Set (V × V)}
    (hpoint : Function.Injective point)
    (hsource : Function.Injective source)
    (htarget : Function.Injective target)
    (hedge : ∀ {a b}, (a, b) ∈ E →
      ∃ i, a = point (source i) ∧ b = point (target i)) :
    Relator.BiUnique (fun a b ↦ (a, b) ∈ E) := by
  constructor
  · intro a b c hac hbc
    obtain ⟨i, hai, hci⟩ := hedge hac
    obtain ⟨j, hbj, hcj⟩ := hedge hbc
    have hij : i = j := htarget (hpoint (hci.symm.trans hcj))
    subst j
    exact hai.trans hbj.symm
  · intro a b c hab hac
    obtain ⟨i, hai, hbi⟩ := hedge hab
    obtain ⟨j, haj, hcj⟩ := hedge hac
    have hij : i = j := hsource (hpoint (hai.symm.trans haj))
    subst j
    exact hbi.trans hcj.symm

/-- The ordered contacts which become vertices of the compressed segment
chain. -/
def contactSet
    (S : ContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) : Set V :=
  match S with
  | .finite T => Set.range T.point
  | .eventuallyOutside T => Set.range T.point
  | .omega T => Set.range T.point

def ClosedBlocksRealizedBy
    (S : ContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) (E : Set (V × V)) : Prop :=
  match S with
  | .finite T => T.ClosedBlocksRealizedBy E
  | .eventuallyOutside T => T.ClosedBlocksRealizedBy E
  | .omega T => T.ClosedBlocksRealizedBy E

/-- All Claim-2 compressions contributed by one segmented route. -/
def compressedOutsideEdges
    (S : ContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) : Set (V × V) :=
  match S with
  | .finite T => T.compressedOutsideEdges
  | .eventuallyOutside T => T.compressedOutsideEdges
  | .omega T => T.compressedOutsideEdges

theorem compressedOutsideEdges_subset_imaginaryGraph
    (S : ContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily)
    {kappa : Cardinal.{u}}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    S.compressedOutsideEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  cases S with
  | finite T => exact T.compressedOutsideEdges_subset_imaginaryGraph hclosed
  | eventuallyOutside T =>
      exact T.compressedOutsideEdges_subset_imaginaryGraph hclosed
  | omega T => exact T.compressedOutsideEdges_subset_imaginaryGraph hclosed

theorem endpoints_mem_contactSet_of_mem_compressedOutsideEdges
    (S : ContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) {a b : V} (hab : (a, b) ∈ S.compressedOutsideEdges) :
    a ∈ S.contactSet ∧ b ∈ S.contactSet := by
  cases S with
  | finite T =>
      rcases hab with ⟨i, P, _hi, h⟩
      exact ⟨⟨i.castSucc, (congrArg Prod.fst h).symm⟩,
        ⟨i.succ, (congrArg Prod.snd h).symm⟩⟩
  | eventuallyOutside T =>
      rcases hab with ⟨i, P, _hi, h⟩
      exact ⟨⟨i.castSucc, (congrArg Prod.fst h).symm⟩,
        ⟨i.succ, (congrArg Prod.snd h).symm⟩⟩
  | omega T =>
      rcases hab with ⟨i, P, _hi, h⟩
      exact ⟨⟨i, (congrArg Prod.fst h).symm⟩,
        ⟨i + 1, (congrArg Prod.snd h).symm⟩⟩

theorem compressedOutsideEdges_biUnique
    (S : ContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) :
    Relator.BiUnique (fun a b ↦ (a, b) ∈ S.compressedOutsideEdges) := by
  cases S with
  | finite T =>
      apply indexedEdges_biUnique
        (I := Fin T.count) (J := Fin (T.count + 1))
        (point := T.point) (source := fun i : Fin T.count ↦ i.castSucc)
        (target := fun i : Fin T.count ↦ i.succ) T.point_injective
      · intro i j hij
        exact Fin.castSucc_injective _ hij
      · intro i j hij
        exact Fin.succ_injective _ hij
      · intro a b hab
        rcases hab with ⟨i, P, _hi, h⟩
        exact ⟨i, congrArg Prod.fst h, congrArg Prod.snd h⟩
  | eventuallyOutside T =>
      apply indexedEdges_biUnique
        (I := Fin T.count) (J := Fin (T.count + 1))
        (point := T.point) (source := fun i : Fin T.count ↦ i.castSucc)
        (target := fun i : Fin T.count ↦ i.succ) T.point_injective
      · intro i j hij
        exact Fin.castSucc_injective _ hij
      · intro i j hij
        exact Fin.succ_injective _ hij
      · intro a b hab
        rcases hab with ⟨i, P, _hi, h⟩
        exact ⟨i, congrArg Prod.fst h, congrArg Prod.snd h⟩
  | omega T =>
      apply indexedEdges_biUnique
        (I := ℕ) (J := ℕ) (point := T.point) (source := id)
        (target := fun i ↦ i + 1) T.point_injective
      · exact Function.injective_id
      · exact fun _ _ h ↦ Nat.succ.inj h
      · intro a b hab
        rcases hab with ⟨i, P, _hi, h⟩
        exact ⟨i, congrArg Prod.fst h, congrArg Prod.snd h⟩

end ContactSegmentation

/-- Parallel replacement for the false global `AssignmentClosureContext`.
It retains the genuine simultaneous assignment and segments each one of its
routes before any Claim-2 compression is attempted. -/
structure ContactSegmentedAssignment
    {Z : Set Gamma.DPath} (A : SimultaneousAssignment Z Y)
    (X before innerRoof outerRoof : Set V)
    (closureFamily : Set Gamma.DPath) where
  segmentation : ∀ s, ContactSegmentation (Y := Y) (A.assigned s) X before
    innerRoof outerRoof closureFamily
  contacts_pairwiseDisjoint : ∀ s t, s ≠ t →
    Disjoint (segmentation s).contactSet (segmentation t).contactSet

namespace ContactSegmentedAssignment

variable {Z : Set Gamma.DPath} {A : SimultaneousAssignment Z Y}

/-- The whole-family transaction compresses every outside-open segment, not
one edge per source. -/
def compressedOutsideEdges
    (S : ContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily) : Set (V × V) :=
  ⋃ s, (S.segmentation s).compressedOutsideEdges

theorem compressedOutsideEdges_subset_imaginaryGraph
    (S : ContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily)
    {kappa : Cardinal.{u}}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    S.compressedOutsideEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  simp only [compressedOutsideEdges, Set.mem_iUnion] at he
  obtain ⟨s, he⟩ := he
  exact (S.segmentation s).compressedOutsideEdges_subset_imaginaryGraph
    hclosed he

/-- Orbit-disjoint contact ownership upgrades the per-route chains to one
bi-unique compressed relation. -/
theorem compressedOutsideEdges_biUnique
    (S : ContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily) :
    Relator.BiUnique (fun a b ↦ (a, b) ∈ S.compressedOutsideEdges) := by
  constructor
  · intro a b c hac hbc
    simp only [compressedOutsideEdges, Set.mem_iUnion] at hac hbc
    obtain ⟨s, hac⟩ := hac
    obtain ⟨t, hbc⟩ := hbc
    by_cases hst : s = t
    · subst t
      exact (S.segmentation s).compressedOutsideEdges_biUnique.1 hac hbc
    · exfalso
      have hcs :=
        (S.segmentation s).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
          hac |>.2
      have hct :=
        (S.segmentation t).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
          hbc |>.2
      exact Set.disjoint_left.1 (S.contacts_pairwiseDisjoint s t hst) hcs hct
  · intro a b c hab hac
    simp only [compressedOutsideEdges, Set.mem_iUnion] at hab hac
    obtain ⟨s, hab⟩ := hab
    obtain ⟨t, hac⟩ := hac
    by_cases hst : s = t
    · subst t
      exact (S.segmentation s).compressedOutsideEdges_biUnique.2 hab hac
    · exfalso
      have has :=
        (S.segmentation s).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
          hab |>.1
      have hat :=
        (S.segmentation t).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
          hac |>.1
      exact Set.disjoint_left.1 (S.contacts_pairwiseDisjoint s t hst) has hat

/-- Exact downstream obligation for turning the contact compression into one
blueprint relation.

`closedEdges` means the already oriented inside relation retained by the
ambient transaction.  In particular it does **not** realize a backward
reference block in the direction in which the alternating route traverses
it: safe switching deletes those backward edges, and the four-vertex audit
above shows that a directed path in the traversal direction need not exist.
The earlier `realizes_closed` field therefore encoded a false obligation and
has deliberately been removed. -/
structure TransactionGeometry
    (S : ContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily) where
  closedEdges : Set (V × V)
  closedEdges_in_graph : closedEdges ⊆ {e | Gamma.graph.Adj e.1 e.2}
  biunique : Relator.BiUnique (fun a b ↦
    (a, b) ∈ closedEdges ∪ S.compressedOutsideEdges)
  acyclic : ¬ ContainsDirectedCycle
    (closedEdges ∪ S.compressedOutsideEdges)
  no_reverse_ray : ¬ ContainsReverseDirectedRay
    (closedEdges ∪ S.compressedOutsideEdges)

end ContactSegmentedAssignment

/-! ## Closed owner paths and retained row edges -/

/-- Along an edge owned by a path family closed at `X`, either both
endpoints belong to `X` or neither does. -/
theorem mem_closed_iff_of_mem_familyEdges
    (hclosed : ClosedUnderPaths Gamma W X) {a b : V}
    (hab : (a, b) ∈ familyEdges W) :
    a ∈ X ↔ b ∈ X := by
  simp only [familyEdges, Set.mem_iUnion] at hab
  obtain ⟨p, hpW, habp⟩ := hab
  have habSupport := p.edgeSet_subset_support_prod habp
  constructor
  · intro ha
    exact hclosed p hpW ⟨a, habSupport.1, ha⟩ habSupport.2
  · intro hb
    exact hclosed p hpW ⟨b, habSupport.2, hb⟩ habSupport.1

/-- Every endpoint of an edge retained by the outside cut is outside the
closed set. -/
theorem outsideFamilyEdges_endpoints_not_mem
    (hclosed : ClosedUnderPaths Gamma W X) {a b : V}
    (hab : (a, b) ∈ outsideFamilyEdges W X) :
    a ∉ X ∧ b ∉ X := by
  have hsame : a ∈ X ↔ b ∈ X :=
    mem_closed_iff_of_mem_familyEdges hclosed
      (outsideFamilyEdges_subset W X hab)
  have hnotBoth : ¬ (a ∈ X ∧ b ∈ X) := by
    exact hab.2
  constructor
  · intro ha
    exact hnotBoth ⟨ha, hsame.mp ha⟩
  · intro hb
    exact hnotBoth ⟨hsame.mpr hb, hb⟩

/-- Every vertex of a nontrivial finite path is incident with one of its
edges. -/
theorem finitePath_mem_support_incident_of_nontrivial
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish)
    {x : V} (hx : x ∈ p.support) :
    (∃ y, (x, y) ∈ p.edgeSet) ∨ ∃ y, (y, x) ∈ p.edgeSet := by
  by_cases hfinish : x = p.finish
  · right
    apply Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
      p hx
    intro hstart
    apply hne
    exact hstart.symm.trans hfinish
  · left
    exact Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      p hx hfinish

/-- A nontrivial finite path all of whose edges are retained outside edges
has support disjoint from the closed set. -/
theorem finitePath_support_disjoint_of_edges_subset_outside
    (hclosed : ClosedUnderPaths Gamma W X)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish)
    (hedges : p.edgeSet ⊆ outsideFamilyEdges W X) :
    Disjoint p.support X := by
  rw [Set.disjoint_left]
  intro x hxp hxX
  rcases finitePath_mem_support_incident_of_nontrivial p hne hxp with
      ⟨y, hxy⟩ | ⟨y, hyx⟩
  · exact (outsideFamilyEdges_endpoints_not_mem hclosed
      (hedges hxy)).1 hxX
  · exact (outsideFamilyEdges_endpoints_not_mem hclosed
      (hedges hyx)).2 hxX

/-! ## Linkwise exclusion of re-entry -/

/-- A fragment of a closed owner path which contains one point outside
`X` is wholly outside `X`. -/
theorem fragment_support_disjoint_of_closed_of_mem_not_mem
    (hclosed : ClosedUnderPaths Gamma Y X)
    {p : FinitePath Gamma.graph} (hp : IsFragmentOf p Y)
    {a : V} (hap : a ∈ p.support) (haX : a ∉ X) :
    Disjoint p.support X := by
  rcases hp with ⟨q, hqY, hpq⟩
  rw [Set.disjoint_left]
  intro x hxp hxX
  have hqInside : q.support ⊆ X :=
    hclosed q hqY ⟨x, hpq.1 hxp, hxX⟩
  exact haX (hqInside (hpq.1 hap))

/-- Every forward link of a bracket assignment on the literal outside cut
is disjoint from the closed set. -/
theorem forwardLink_support_disjoint
    {F : OutsideFracturedWarp W X} (hclosed : ClosedUnderPaths Gamma W X)
    {Q : AltPath Gamma.graph}
    (hQ : IsBracketAlternating F.holes.edgeWarp Y Q)
    {l : Link Gamma.graph} (hl : l ∈ Q.links)
    (hforward : l.direction = .forward) :
    Disjoint l.path.support X := by
  apply finitePath_support_disjoint_of_edges_subset_outside hclosed
    l.path l.nontrivial
  intro e he
  have heFamily : e ∈ familyEdges F.holes.edgeWarp :=
    edgeSet_subset_familyEdges_of_isFragmentOf (hQ.2 l hl hforward) he
  rwa [F.edgeWarp_familyEdges] at heFamily

/-- At the actual row-closed cut, a bracket-safe path starting at a literal
outside source has no vertex in the closed set.  The proof treats finite and
infinite traces separately only to expose their predecessor link; its
mathematical content is the same first-entry argument in both cases. -/
theorem bracketPath_vertexSet_disjoint_of_rowClosed
    {F : OutsideFracturedWarp W X}
    (hrow : ClosedUnderPaths Gamma W X)
    (hreference : ClosedUnderPaths Gamma Y X)
    {Q : AltPath Gamma.graph}
    (hQ : IsBracketSafe F.holes.edgeWarp Y Q)
    (hinitial : Q.initial ∉ X) :
    Disjoint Q.vertexSet X := by
  have hforward : ∀ {l : Link Gamma.graph}, l ∈ Q.links →
      l.direction = .forward → Disjoint l.path.support X := by
    intro l hl hdir
    exact forwardLink_support_disjoint hrow
      hQ.isBracketAlternating hl hdir
  cases Q with
  | trivial v =>
      simpa [AltPath.vertexSet, AltPath.initial, Set.disjoint_singleton_left]
        using hinitial
  | finite T =>
      have hlink : ∀ i : Fin (T.lastIndex + 1),
          Disjoint (T.link i).path.support X := by
        intro i
        cases hdir : (T.link i).direction with
        | forward =>
            apply hforward
            · exact ⟨i, rfl⟩
            · exact hdir
        | backward =>
            have hentry : (T.link i).entry ∉ X := by
              by_cases hi : i.1 = 0
              · have hi0 : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext hi
                subst i
                exact hinitial
              · have hiPos : 0 < i.1 := Nat.pos_of_ne_zero hi
                let j : Fin T.lastIndex := ⟨i.1 - 1, by omega⟩
                have hsucc : j.succ = i := by
                  apply Fin.ext
                  simp [j]
                  omega
                have hprevDir : (T.link j.castSucc).direction = .forward := by
                  cases hp : (T.link j.castSucc).direction with
                  | forward => rfl
                  | backward =>
                      exfalso
                      apply T.alternates j
                      rw [hsucc, hp, hdir]
                have hprev := hforward
                  (l := T.link j.castSucc) ⟨j.castSucc, rfl⟩ hprevDir
                rw [← hsucc, ← T.joins j]
                exact Set.disjoint_left.1 hprev
                  (T.link j.castSucc).exit_mem_support
            apply fragment_support_disjoint_of_closed_of_mem_not_mem
              hreference (hQ.isAlternating.2.1 (T.link i) ⟨i, rfl⟩ hdir)
              (T.link i).entry_mem_support hentry
      rw [Set.disjoint_left]
      intro x hx hxX
      simp only [AltPath.vertexSet, FiniteTrace.vertexSet,
        Set.mem_iUnion] at hx
      obtain ⟨i, hxi⟩ := hx
      exact Set.disjoint_left.1 (hlink i) hxi hxX
  | infinite T =>
      have hlink : ∀ i : ℕ, Disjoint (T.link i).path.support X := by
        intro i
        cases hdir : (T.link i).direction with
        | forward =>
            apply hforward
            · exact ⟨i, rfl⟩
            · exact hdir
        | backward =>
            have hentry : (T.link i).entry ∉ X := by
              cases i with
              | zero => exact hinitial
              | succ j =>
                  have hprevDir : (T.link j).direction = .forward := by
                    cases hp : (T.link j).direction with
                    | forward => rfl
                    | backward =>
                        exfalso
                        apply T.alternates j
                        rw [hp, hdir]
                  have hprev := hforward
                    (l := T.link j) ⟨j, rfl⟩ hprevDir
                  rw [← T.joins j]
                  exact Set.disjoint_left.1 hprev
                    (T.link j).exit_mem_support
            apply fragment_support_disjoint_of_closed_of_mem_not_mem
              hreference (hQ.isAlternating.2.1 (T.link i) ⟨i, rfl⟩ hdir)
              (T.link i).entry_mem_support hentry
      rw [Set.disjoint_left]
      intro x hx hxX
      simp only [AltPath.vertexSet, InfiniteTrace.vertexSet,
        Set.mem_iUnion] at hx
      obtain ⟨i, hxi⟩ := hx
      exact Set.disjoint_left.1 (hlink i) hxi hxX

/-! ## The post-closure selected-cut transaction -/

/-- The initial vertex of every literal outside hole is outside `X` once
the row is closed at `X`. -/
theorem OutsideFracturedWarp.initial_not_mem_of_rowClosed
    (F : OutsideFracturedWarp W X)
    (hrow : ClosedUnderPaths Gamma W X) {x : V}
    (hx : x ∈ Gamma.initialSet F.holes.paths) : x ∉ X := by
  have hxVertex : x ∈ Gamma.vertexSet F.holes.paths := by
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p, hp, hpx ▸ p.initial_mem_support⟩
  rw [F.vertexSet_eq] at hxVertex
  exact Set.disjoint_left.1
    (outsideCarrier_disjoint_of_closedUnderPaths W X hrow) hxVertex

/-- The bracket-provenance assignment supplied by the fractured projection
compiler is already the required closed-set-avoiding replacement at the
actual row-closed set. -/
def ClosedSetAvoidingReplacement.ofBracketFracturedAssignment
    {F : OutsideFracturedWarp W X}
    (hrow : ClosedUnderPaths Gamma W X)
    (hreference : ClosedUnderPaths Gamma Y X)
    (B : FracturedAssignmentPeel.BracketFracturedAssignment F.holes Y) :
    ClosedSetAvoidingReplacement B.assignment X where
  path := B.assignment.assigned
  starts_at := B.assignment.starts_at
  safe := B.assignment.safe
  terminal_eq := fun _ ↦ rfl
  interior_disjoint_finite := by
    intro s v _hterm
    apply Set.disjoint_of_subset_left (fun x hx ↦ hx.1)
    apply bracketPath_vertexSet_disjoint_of_rowClosed hrow hreference
      (B.bracket_safe s)
    rw [B.assignment.starts_at s]
    exact F.initial_not_mem_of_rowClosed hrow s.property.1
  interior_disjoint_infinite := by
    intro s _hinfinite
    apply Set.disjoint_of_subset_left (fun x hx ↦ hx.1)
    apply bracketPath_vertexSet_disjoint_of_rowClosed hrow hreference
      (B.bracket_safe s)
    rw [B.assignment.starts_at s]
    exact F.initial_not_mem_of_rowClosed hrow s.property.1
  outside := by
    intro s hinside
    have hinitialVertex : (B.assignment.assigned s).initial ∈
        (B.assignment.assigned s).vertexSet :=
      (B.assignment.assigned s).initial_mem_vertexSet
    have hinitialX := hinside hinitialVertex
    rw [B.assignment.starts_at s] at hinitialX
    exact F.initial_not_mem_of_rowClosed hrow s.property.1 hinitialX

/-- Conditional one-edge constructor under closure of the *later linkage*
itself.  This is a useful diagnostic theorem, but its `hrow` premise is not
produced by Assertions 9.22--9.25 and it must not be used for Assertion 9.31.
The contact-segmented structures above only isolate the additional
construction obligations; the checked obstruction shows that Claim 1 alone
does not construct them. -/
theorem SelectedClosedFracturedCut.exists_of_literalOutsideCut_and_rowClosure
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (hrow : ClosedUnderPaths Gamma W X)
    (hreference : ClosedUnderPaths Gamma Y X)
    (boundary : ∀ _F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      OutsideCutBoundary (Y := Y) W X before innerRoof outerRoof)
    (assigned : ∀ F :
      OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X,
      FracturedAssignmentPeel.BracketFracturedAssignment
        F.outside.holes Y) :
    Nonempty (SelectedClosedFracturedCut
      (Gamma := Gamma) (Y := Y) X before innerRoof outerRoof) := by
  apply SelectedClosedFracturedCut.exists_of_literalOutsideCut_and_avoidingReplacement
      hW hfinite boundary (fun F ↦ (assigned F).assignment)
  intro F
  exact ClosedSetAvoidingReplacement.ofBracketFracturedAssignment
    hrow hreference (assigned F)

end LinkageBlueprint
end Blueprint
end Erdos599
