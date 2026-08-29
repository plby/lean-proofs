/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PopularAuxiliary

/-!
# Decoding paths in the Section 8 auxiliary web

The vertices of `Input.lambda` are gadgets.  An ordinary vertex represents
itself, while the vertex `edge u v` represents traversal of the ladder edge
`u -> v` in the reverse direction, from `v` to `u`.  Between two consecutive
gadgets an auxiliary arc either represents one forward edge of the original
digraph, or the equality which joins two consecutive reversed ladder edges.

This file makes that correspondence literal.  In particular, it constructs
the raw switched edge data attached to a finite auxiliary path and proves the
exact transports of avoidance used in Assertions 8.18--8.22.  Turning a
decoded route into the maximal-link presentation of `Alternating.AltPath`
requires only coalescing consecutive forward connectors; no graph-theoretic
witness is hidden in the definitions below.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary

open Set DirectedPath
open Alternating

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

namespace Input

variable (L : Input Gamma I)

abbrev LV (_L : Input Gamma I) := LambdaVertex V I

/-! ## The endpoint-relaxed alternating predicate -/

/-- The literal link-and-endpoint content of source Definition 4.2, with the
final endpoint condition relaxed.  `FiniteTrace` itself supplies alternating
directions, joins, and all of the source's collision clauses.  In particular,
the published definition does not require the strengthened maximal-contact
or forward-edge clauses built into this development's `IsAlternating`. -/
def IsSourceTerminalRelaxedAlternating
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (Q : AltPath Gamma.graph) : Prop :=
  Gamma.IsWarp Y ∧ BackwardLinksOn Y Q ∧
    (Q.firstDirection? = some .forward → Q.initial ∉ Gamma.vertexSet Y)

/-- The literal finite-terminal version of source Definition 4.2. -/
def IsSourceAlternating
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (Q : AltPath Gamma.graph) : Prop :=
  IsSourceTerminalRelaxedAlternating Gamma Y Q ∧
    ∀ t, Q.terminal? = some t → Q.lastDirection? = some .forward →
      t ∉ Gamma.vertexSet Y

theorem IsSourceAlternating.terminalRelaxed
    {Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hQ : IsSourceAlternating Gamma Y Q) :
    IsSourceTerminalRelaxedAlternating Gamma Y Q := hQ.1

theorem IsSourceTerminalRelaxedAlternating.isSourceAlternating_of_terminal_not_mem
    {Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hQ : IsSourceTerminalRelaxedAlternating Gamma Y Q) {t : V}
    (hterminal : Q.terminal? = some t) (ht : t ∉ Gamma.vertexSet Y) :
    IsSourceAlternating Gamma Y Q := by
  refine ⟨hQ, ?_⟩
  intro s hs _hlast
  have hst : s = t := Option.some.inj (hs.symm.trans hterminal)
  exact hst ▸ ht

/-- The strengthened off-warp and maximal-contact facts turn the literal
source predicate into the repository's switching-ready predicate. -/
theorem IsSourceAlternating.isAlternating
    {Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hQ : IsSourceAlternating Gamma Y Q)
    (hoff : ForwardLinksOff Y Q)
    (_hcontacts : ForwardVertexContactsCovered Y Q) :
    IsAlternating Y Q :=
  ⟨hQ.1.1, hQ.1.2.1, hQ.1.2.2, hQ.2⟩

/-- Bracketed literal source alternation. -/
def IsSourceBracketAlternating
    (Gamma : DWeb V) (U Y : Set Gamma.DPath) (Q : AltPath Gamma.graph) : Prop :=
  IsSourceAlternating Gamma Y Q ∧
    ∀ l ∈ Q.links, l.direction = .forward → IsFragmentOf l.path U

theorem IsSourceBracketAlternating.isBracketAlternating
    {U Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hQ : IsSourceBracketAlternating Gamma U Y Q)
    (hoff : ForwardLinksOff Y Q)
    (hcontacts : ForwardVertexContactsCovered Y Q) :
    IsBracketAlternating U Y Q :=
  ⟨hQ.1.isAlternating hoff hcontacts, hQ.2⟩

/-- The Section 8 conversion stops when it first reaches a target marker on
the reference ladder.  Consequently its final forward link may meet the
reference warp at its terminal, before a backward link through that warp is
started.  This is the exact terminal-relaxed version of the maximal-contact
clause in `Alternating.IsAlternating`. -/
def ForwardVertexContactsCoveredAtTerminal
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (Q : AltPath Gamma.graph) : Prop :=
  ∀ {x}, x ∈ Q.directionVertices .forward →
    x ∈ Gamma.vertexSet Y →
      x ∈ Q.directionVertices .backward ∨ Q.terminal? = some x

/-- Alternation with the final target contact left unexpanded.  All source
conditions and all nonterminal contacts are exactly those of Definition
4.2; only the terminal contact is relaxed. -/
def IsTerminalRelaxedAlternating
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (Q : AltPath Gamma.graph) : Prop :=
  Gamma.IsWarp Y ∧ BackwardLinksOn Y Q ∧ ForwardLinksOff Y Q ∧
    ForwardVertexContactsCoveredAtTerminal Gamma Y Q ∧
    (Q.firstDirection? = some .forward → Q.initial ∉ Gamma.vertexSet Y)

/-- If the finite terminal is outside the reference warp, terminal-relaxed
alternation is ordinary alternation. -/
theorem IsTerminalRelaxedAlternating.isAlternating_of_terminal_not_mem
    {Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hQ : IsTerminalRelaxedAlternating Gamma Y Q) {t : V}
    (hterminal : Q.terminal? = some t) (ht : t ∉ Gamma.vertexSet Y) :
    IsAlternating Y Q := by
  refine ⟨hQ.1, hQ.2.1, hQ.2.2.2.2, ?_⟩
  · intro s hs _hlast
    have hst : s = t := Option.some.inj (hs.symm.trans hterminal)
    exact hst ▸ ht

/-- The bracketed variant used when the forward links are fragments of a
second warp. -/
def IsTerminalRelaxedBracketAlternating
    (Gamma : DWeb V) (U Y : Set Gamma.DPath) (Q : AltPath Gamma.graph) : Prop :=
  IsTerminalRelaxedAlternating Gamma Y Q ∧
    ∀ l ∈ Q.links, l.direction = .forward → IsFragmentOf l.path U

theorem IsTerminalRelaxedBracketAlternating.isBracketAlternating_of_terminal_not_mem
    {U Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hQ : IsTerminalRelaxedBracketAlternating Gamma U Y Q) {t : V}
    (hterminal : Q.terminal? = some t) (ht : t ∉ Gamma.vertexSet Y) :
    IsBracketAlternating U Y Q :=
  ⟨hQ.1.isAlternating_of_terminal_not_mem hterminal ht, hQ.2⟩

/-! ## The two ends of a gadget -/

/-- The original vertex at which a non-proxy gadget is entered.  A ladder
edge `u -> v` is entered at its head `v`, because that edge is traversed
backwards by the alternating route. -/
def gadgetEntry (L : Input Gamma I) : L.LV → Option V
  | .old x => some x
  | .edge _ v => some v
  | .proxy _ => none

/-- The original vertex at which a non-proxy gadget is left.  A ladder edge
`u -> v` is left at its tail `u`. -/
def gadgetExit (L : Input Gamma I) : L.LV → Option V
  | .old x => some x
  | .edge u _ => some u
  | .proxy _ => none

/-- The ladder edge traversed backwards inside a gadget. -/
def gadgetBackwardEdge (L : Input Gamma I) : L.LV → Option (V × V)
  | .edge u v => some (u, v)
  | _ => none

@[simp] theorem gadgetEntry_old (x : V) :
    L.gadgetEntry (.old x) = some x := rfl

@[simp] theorem gadgetEntry_edge (u w : V) :
    L.gadgetEntry (.edge u w) = some w := rfl

@[simp] theorem gadgetEntry_proxy (i : I) :
    L.gadgetEntry (.proxy i) = none := rfl

@[simp] theorem gadgetExit_old (x : V) :
    L.gadgetExit (.old x) = some x := rfl

@[simp] theorem gadgetExit_edge (u w : V) :
    L.gadgetExit (.edge u w) = some u := rfl

@[simp] theorem gadgetExit_proxy (i : I) :
    L.gadgetExit (.proxy i) = none := rfl

@[simp] theorem gadgetBackwardEdge_old (x : V) :
    L.gadgetBackwardEdge (.old x) = none := rfl

@[simp] theorem gadgetBackwardEdge_edge (u w : V) :
    L.gadgetBackwardEdge (.edge u w) = some (u, w) := rfl

@[simp] theorem gadgetBackwardEdge_proxy (i : I) :
    L.gadgetBackwardEdge (.proxy i) = none := rfl

/-! ## Decoding one auxiliary arc -/

/-- A genuine forward connector represented by an auxiliary arc.  At a
proxy the first endpoint may be any vertex of the represented ray; at an
ordinary or edge gadget it is the gadget exit. -/
def ForwardConnector (a b : L.LV) (x y : V) : Prop :=
  (L.gadgetExit a = some x ∨
      ∃ i : I, a = .proxy i ∧ x ∈ (L.proxyPath i).support) ∧
    L.gadgetEntry b = some y ∧ Gamma.graph.Adj x y

/-- A zero-length equality join at a reversed ladder edge.  Besides two
consecutive reversed edge gadgets, this includes entering the first reversed
edge from its head and leaving the last reversed edge at its tail.  These
endpoint joins are needed to reverse a troublesome finite path beginning at
its terminal. -/
def BackwardJoin (a b : L.LV) : Prop :=
  (∃ u v, a = .edge u v ∧ b = .old u ∧
      (u, v) ∈ L.familyEdges) ∨
    (∃ u v, a = .old v ∧ b = .edge u v ∧
      (u, v) ∈ L.familyEdges) ∨
    ∃ u v w, a = .edge u v ∧ b = .edge w u ∧
      (u, v) ∈ L.familyEdges ∧ (w, u) ∈ L.familyEdges

/-- Every auxiliary arc has exactly the intended graph-level meaning: it is
either a genuine forward original edge or a zero-length join between two
backward ladder-edge gadgets. -/
theorem lambda_adj_decodes {a b : L.LV}
    (hab : L.lambda.graph.Adj a b) :
    (∃ x y, L.ForwardConnector a b x y) ∨ L.BackwardJoin a b := by
  change L.LambdaAdj a b at hab
  rcases hab with hVV | hEV | hVE | hEE | hIV | hIE
  · rcases hVV with ⟨u, w, rfl, rfl, _hu, _hw, huw⟩
    exact Or.inl ⟨u, w, Or.inl rfl, rfl, huw⟩
  · rcases hEV with ⟨u, v, q, rfl, rfl, he, rfl | ⟨_hq, huq⟩⟩
    · exact Or.inr (Or.inl ⟨u, v, rfl, rfl, he⟩)
    · exact Or.inl ⟨u, q, Or.inl rfl, rfl, huq⟩
  · rcases hVE with ⟨q, u, v, rfl, rfl, he, rfl | ⟨_hq, hqv⟩⟩
    · exact Or.inr (Or.inr (Or.inl ⟨u, q, rfl, rfl, he⟩))
    · exact Or.inl ⟨q, v, Or.inl rfl, rfl, hqv⟩
  · rcases hEE with ⟨u, v, w, z, rfl, rfl, huv, hwz, huz | huz⟩
    · subst z
      exact Or.inr (Or.inr (Or.inr ⟨u, v, w, rfl, rfl, huv, hwz⟩))
    · exact Or.inl ⟨u, z, Or.inl rfl, rfl, huz⟩
  · rcases hIV with ⟨i, q, rfl, rfl, _hq, u, hui, huq⟩
    exact Or.inl ⟨u, q, Or.inr ⟨i, rfl, hui⟩, rfl, huq⟩
  · rcases hIE with ⟨i, w, z, rfl, rfl, _he, u, hui, huz⟩
    exact Or.inl ⟨u, z, Or.inr ⟨i, rfl, hui⟩, rfl, huz⟩

/-- A backward join really identifies the exit of the first gadget with the
entry of the second. -/
theorem BackwardJoin.exit_eq_entry {a b : L.LV}
    (h : L.BackwardJoin a b) :
    ∃ x, L.gadgetExit a = some x ∧ L.gadgetEntry b = some x := by
  rcases h with h | h | h
  · rcases h with ⟨u, v, rfl, rfl, _huv⟩
    exact ⟨u, rfl, rfl⟩
  · rcases h with ⟨u, v, rfl, rfl, _huv⟩
    exact ⟨v, rfl, rfl⟩
  · rcases h with ⟨u, v, w, rfl, rfl, _huv, _hwu⟩
    exact ⟨u, rfl, rfl⟩

/-- Both reversed gadgets in a backward join are genuine edges of the
ladder warp. -/
theorem BackwardJoin.edges_mem_familyEdges {a b : L.LV}
    (h : L.BackwardJoin a b) :
    (∀ e, L.gadgetBackwardEdge a = some e → e ∈ L.familyEdges) ∧
      ∀ e, L.gadgetBackwardEdge b = some e → e ∈ L.familyEdges := by
  rcases h with h | h | h
  · rcases h with ⟨u, v, rfl, rfl, huv⟩
    exact ⟨fun e he ↦ Option.some.inj he ▸ huv, by simp⟩
  · rcases h with ⟨u, v, rfl, rfl, huv⟩
    exact ⟨by simp, fun e he ↦ Option.some.inj he ▸ huv⟩
  · rcases h with ⟨u, v, w, rfl, rfl, huv, hwu⟩
    exact ⟨fun e he ↦ Option.some.inj he ▸ huv,
      fun e he ↦ Option.some.inj he ▸ hwu⟩

/-- No auxiliary arc enters a proxy, hence every proxy occurring after the
first vertex of a directed auxiliary path is impossible. -/
theorem lambda_adj_not_proxy_right {a : L.LV} {i : I}
    (h : L.lambda.graph.Adj a (.proxy i)) : False :=
  L.lambda_not_adj_to_proxy a i h

/-- A proof-relevant expansion of one auxiliary arc.  It records either the
unique kind of edge that is inserted into the original graph, or the
edge-free join between two reversed ladder gadgets. -/
inductive ArcExpansion (a b : L.LV) : Type (max u v)
  | forward (x y : V) (valid : L.ForwardConnector a b x y)
  | backwardJoin (valid : L.BackwardJoin a b)

/-- Every auxiliary arc has a proof-relevant expansion. -/
theorem exists_arcExpansion {a b : L.LV}
    (h : L.lambda.graph.Adj a b) : Nonempty (L.ArcExpansion a b) := by
  rcases L.lambda_adj_decodes h with ⟨x, y, hxy⟩ | hjoin
  · exact ⟨.forward x y hxy⟩
  · exact ⟨.backwardJoin hjoin⟩

/-- Choose one concrete expansion of an auxiliary arc.  The only
non-uniqueness is the attachment point of a proxy on its represented ray. -/
noncomputable def chooseArcExpansion {a b : L.LV}
    (h : L.lambda.graph.Adj a b) : L.ArcExpansion a b :=
  Classical.choice (L.exists_arcExpansion h)

/-- The selected genuine forward connector of an auxiliary arc, if that
arc is not a zero-length backward join. -/
noncomputable def chosenConnector? (a b : L.LV) : Option (V × V) :=
  by
    classical
    exact if h : L.lambda.graph.Adj a b then
      match L.chooseArcExpansion h with
      | .forward x y _ => some (x, y)
      | .backwardJoin _ => none
    else none

theorem chosenConnector?_eq_some {a b : L.LV} {e : V × V}
    (h : L.chosenConnector? a b = some e) :
    L.ForwardConnector a b e.1 e.2 := by
  classical
  simp only [chosenConnector?] at h
  split at h
  next hab =>
    cases hexp : L.chooseArcExpansion hab with
    | forward x y hxy =>
        rw [hexp] at h
        have he : (x, y) = e := Option.some.inj h
        subst e
        exact hxy
    | backwardJoin hjoin =>
        rw [hexp] at h
        cases h
  next hab => cases h

theorem chosenConnector?_eq_none_of_adj {a b : L.LV}
    (hab : L.lambda.graph.Adj a b)
    (h : L.chosenConnector? a b = none) : L.BackwardJoin a b := by
  classical
  simp only [chosenConnector?, dif_pos hab] at h
  cases hexp : L.chooseArcExpansion hab with
  | forward x y hxy =>
      rw [hexp] at h
      cases h
  | backwardJoin hjoin => exact hjoin

/-! ## Edge data decoded from a finite auxiliary path -/

variable (p : FinitePath L.lambda.graph)

/-- Old original vertices explicitly visited by the auxiliary path. -/
def oldVertices : Set V :=
  {x | LambdaVertex.old x ∈ p.support}

/-- Ladder edges whose representing vertices are visited by the auxiliary
path.  Membership in `familyEdges` is retained in the definition, so the
set is usable even for a degenerate one-vertex path not arising between the
source and target. -/
def representedEdges : Set (V × V) :=
  {e | LambdaVertex.edge e.1 e.2 ∈ p.support ∧ e ∈ L.familyEdges}

/-- Genuine forward original edges represented by the arcs of the
auxiliary path.  This definition retains every possible first attachment
when a proxy arc has more than one witness.  A later switching construction
may select one such witness; all of them are genuine original edges. -/
def connectorEdges : Set (V × V) :=
  {e | ∃ a b, (a, b) ∈ p.edgeSet ∧ L.ForwardConnector a b e.1 e.2}

/-- A single, proof-irrelevant selection of the forward connector carried by
each auxiliary path edge.  This is the edge set used by the concrete switch;
unlike `connectorEdges`, a proxy arc contributes exactly one edge. -/
def selectedConnectorEdges : Set (V × V) :=
  {e | ∃ a b, (a, b) ∈ p.edgeSet ∧ L.chosenConnector? a b = some e}

theorem representedEdges_subset_familyEdges :
    L.representedEdges p ⊆ L.familyEdges := by
  intro e he
  exact he.2

theorem connectorEdges_subset_adj :
    L.connectorEdges p ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  rintro e ⟨a, b, _hab, he⟩
  exact he.2.2

theorem selectedConnectorEdges_subset_connectorEdges :
    L.selectedConnectorEdges p ⊆ L.connectorEdges p := by
  rintro e ⟨a, b, hab, he⟩
  exact ⟨a, b, hab, L.chosenConnector?_eq_some he⟩

theorem selectedConnectorEdges_subset_adj :
    L.selectedConnectorEdges p ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
  (L.selectedConnectorEdges_subset_connectorEdges p).trans
    (L.connectorEdges_subset_adj p)

/-- With the selected proxy attachment, every auxiliary path edge has one
and only one of the two kinds of decoded contribution. -/
theorem path_edge_selected_decodes {a b : L.LV}
    (hab : (a, b) ∈ p.edgeSet) :
    (∃ e ∈ L.selectedConnectorEdges p,
        L.ForwardConnector a b e.1 e.2) ∨
      L.BackwardJoin a b := by
  have hadj : L.lambda.graph.Adj a b := p.edgeSet_subset_adj hab
  cases hopt : L.chosenConnector? a b with
  | none => exact Or.inr (L.chosenConnector?_eq_none_of_adj hadj hopt)
  | some e =>
      exact Or.inl ⟨e, ⟨a, b, hab, hopt⟩,
        L.chosenConnector?_eq_some hopt⟩

/-- Every arc of the auxiliary path decodes either to one of its forward
connector edges or to a backward join. -/
theorem path_edge_decodes {a b : L.LV} (hab : (a, b) ∈ p.edgeSet) :
    (∃ e ∈ L.connectorEdges p, L.ForwardConnector a b e.1 e.2) ∨
      L.BackwardJoin a b := by
  have hadj : L.lambda.graph.Adj a b := p.edgeSet_subset_adj hab
  rcases L.lambda_adj_decodes hadj with ⟨x, y, hxy⟩ | hjoin
  · exact Or.inl ⟨(x, y), ⟨a, b, hab, hxy⟩, hxy⟩
  · exact Or.inr hjoin

/-! ## Structural facts about gadgets occurring on a source path -/

theorem familyEdge_of_adj_to_edge {a : L.LV} {u w : V}
    (h : L.lambda.graph.Adj a (.edge u w)) : (u, w) ∈ L.familyEdges := by
  cases a with
  | old x => exact ((L.lambda_adj_old_edge x u w).1 h).1
  | edge r s => exact ((L.lambda_adj_edge_edge r s u w).1 h).2.1
  | proxy i => exact ((L.lambda_adj_proxy_edge i u w).1 h).1

theorem familyEdge_of_adj_from_edge {u w : V} {b : L.LV}
    (h : L.lambda.graph.Adj (.edge u w) b) : (u, w) ∈ L.familyEdges := by
  cases b with
  | old x => exact ((L.lambda_adj_edge_old u w x).1 h).1
  | edge r s => exact ((L.lambda_adj_edge_edge u w r s).1 h).1
  | proxy i => exact False.elim (L.lambda_not_adj_to_proxy (.edge u w) i h)

private theorem Walk.exists_edge_to_of_mem_of_ne_start
    {D : Digraph L.LV} {a b z : L.LV} (q : Walk D a b)
    (hz : z ∈ q.support) (hza : z ≠ a) : ∃ x, (x, z) ∈ q.edgeSet := by
  induction q with
  | nil => exact False.elim (hza (by simpa using hz))
  | @cons a c b h q ih =>
      simp only [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact False.elim (hza rfl)
      · by_cases hzc : z = c
        · exact ⟨a, by simp [hzc]⟩
        · obtain ⟨x, hx⟩ := ih hz hzc
          exact ⟨x, by simp [hx]⟩

/-- Every edge gadget on an auxiliary path which starts in the auxiliary
source represents a genuine edge of the ladder warp. -/
theorem edgeNode_mem_familyEdges_of_start_in_source
    (hstart : p.start ∈ L.lambda.source) {u w : V}
    (huw : LambdaVertex.edge u w ∈ p.support) :
    (u, w) ∈ L.familyEdges := by
  have hne : (LambdaVertex.edge u w : L.LV) ≠ p.start := by
    intro h
    exact L.not_mem_lambda_source_edge u w (h ▸ hstart)
  obtain ⟨a, ha⟩ := Walk.exists_edge_to_of_mem_of_ne_start
    L p.walk huw hne
  exact L.familyEdge_of_adj_to_edge (p.edgeSet_subset_adj ha)

/-- Under the source hypothesis, `representedEdges` is exactly the set of
edge gadgets visited by the path; the explicit family-edge conjunct is then
automatic. -/
theorem mem_representedEdges_iff_of_start_in_source
    (hstart : p.start ∈ L.lambda.source) (e : V × V) :
    e ∈ L.representedEdges p ↔
      LambdaVertex.edge e.1 e.2 ∈ p.support := by
  constructor
  · exact fun he ↦ he.1
  · intro he
    exact ⟨he, L.edgeNode_mem_familyEdges_of_start_in_source p hstart he⟩

/-- A proxy can occur on a source-starting auxiliary path only as its first
vertex, since no auxiliary arc enters a proxy. -/
theorem proxy_mem_support_eq_start (hstart : p.start ∈ L.lambda.source)
    {i : I} (hi : LambdaVertex.proxy i ∈ p.support) :
    p.start = .proxy i := by
  by_contra hne
  obtain ⟨a, ha⟩ := Walk.exists_edge_to_of_mem_of_ne_start
    L p.walk hi (Ne.symm hne)
  exact L.lambda_not_adj_to_proxy a i (p.edgeSet_subset_adj ha)

/-- The original edge set traversed by the decoded alternating route: the
ladder edges represented by edge gadgets together with the selected forward
connectors. -/
def decodedRouteEdges : Set (V × V) :=
  L.representedEdges p ∪ L.selectedConnectorEdges p

theorem decodedRouteEdges_subset_adj :
    L.decodedRouteEdges p ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · have heFamily : e ∈ L.familyEdges :=
      L.representedEdges_subset_familyEdges p he
    rcases heFamily with ⟨q, hq, heq⟩
    exact q.edgeSet_subset_adj heq
  · exact L.selectedConnectorEdges_subset_adj p he

/-- Raw switched edges are the literal symmetric difference prescribed by
source Definition 4.3.  Keeping the symmetric difference here also handles
an unreduced auxiliary path whose selected connector happens to be a ladder
edge; a reduced path later proves that such overlap cannot occur. -/
def decodedSwitchedEdges : Set (V × V) :=
  Alternating.edgeSymmDiff (Alternating.familyEdges L.ladder.paths)
    (L.decodedRouteEdges p)

theorem decodedSwitchedEdges_subset_adj :
    L.decodedSwitchedEdges p ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact Alternating.familyEdges_subset_adj L.ladder.paths he.1
  · exact L.decodedRouteEdges_subset_adj p he.1

/-- The graph-level switch data attached to the decoded route. -/
def decodedSwitchData : Alternating.SwitchData Gamma where
  edges := L.decodedSwitchedEdges p
  edges_in_graph := L.decodedSwitchedEdges_subset_adj p
  isolated := Alternating.isolatedVertices L.ladder.paths

@[simp] theorem decodedSwitchData_edges :
    (L.decodedSwitchData p).edges = L.decodedSwitchedEdges p := rfl

@[simp] theorem decodedSwitchData_isolated :
    (L.decodedSwitchData p).isolated =
      Alternating.isolatedVertices L.ladder.paths := rfl

/-- Any maximal-link compression whose edge set is the decoded route has
exactly the raw application data constructed above.  Thus the combinatorial
run-compression layer need only prove an edge-set identity; all switching
bookkeeping is already discharged here. -/
theorem decodedSwitchData_eq_application_of_edgeSet
    (Q : AltPath Gamma.graph)
    (hQ : Q.edgeSet = L.decodedRouteEdges p) :
    L.decodedSwitchData p =
      Alternating.Cyclowarp.application L.ladder.paths Q := by
  have hedges : (L.decodedSwitchData p).edges =
      (Alternating.Cyclowarp.application L.ladder.paths Q).edges := by
    change L.decodedSwitchedEdges p =
      Alternating.switchedEdges L.ladder.paths Q
    rw [Alternating.switchedEdges_eq_edgeSymmDiff, hQ]
    rfl
  have hisolated : (L.decodedSwitchData p).isolated =
      (Alternating.Cyclowarp.application L.ladder.paths Q).isolated := rfl
  cases hS : L.decodedSwitchData p with
  | mk edges edges_in_graph isolated =>
      cases hT : Alternating.Cyclowarp.application L.ladder.paths Q with
      | mk edges' edges_in_graph' isolated' =>
          have he : edges = edges' := by simpa [hS, hT] using hedges
          have hi : isolated = isolated' := by simpa [hS, hT] using hisolated
          subst edges'
          subst isolated'
          rfl

/-- Consequently any finite-warp realization obtained from an honest
compressed alternating path is already a realization of the decoded
auxiliary switch data. -/
theorem decodedSwitchData_realizedBy_of_application
    (Q : AltPath Gamma.graph) (W : Set Gamma.DPath)
    (hQ : Q.edgeSet = L.decodedRouteEdges p)
    (hW : (Alternating.Cyclowarp.application L.ladder.paths Q).RealizedBy W) :
    (L.decodedSwitchData p).RealizedBy W := by
  rw [L.decodedSwitchData_eq_application_of_edgeSet p Q hQ]
  exact hW

/-! ## Exact avoidance transport -/

/-- Old vertices contained in an auxiliary vertex set. -/
def oldPart (L : Input Gamma I) (C : Set L.LV) : Set V :=
  {x | LambdaVertex.old x ∈ C}

/-- Represented ladder edges contained in an auxiliary vertex set. -/
def edgePart (L : Input Gamma I) (C : Set L.LV) : Set (V × V) :=
  {e | LambdaVertex.edge e.1 e.2 ∈ C}

/-- Proxies contained in an auxiliary vertex set. -/
def proxyPart (L : Input Gamma I) (C : Set L.LV) : Set I :=
  {i | LambdaVertex.proxy i ∈ C}

theorem avoids_oldPart {C : Set L.LV} (hav : L.lambda.Avoids p C) :
    Disjoint (L.oldVertices p) (L.oldPart C) := by
  rw [Set.disjoint_left]
  intro x hxp hxC
  exact Set.disjoint_left.1 hav hxp hxC

theorem avoids_edgePart {C : Set L.LV} (hav : L.lambda.Avoids p C) :
    Disjoint (L.representedEdges p) (L.edgePart C) := by
  rw [Set.disjoint_left]
  intro e hep heC
  exact Set.disjoint_left.1 hav hep.1 heC

/-- Pointwise form of old-vertex avoidance. -/
theorem old_not_mem_of_avoids {C : Set L.LV} (hav : L.lambda.Avoids p C)
    {x : V} (hx : x ∈ L.oldVertices p) : x ∉ L.oldPart C :=
  Set.disjoint_left.1 (L.avoids_oldPart p hav) hx

/-- Pointwise form of represented-edge avoidance. -/
theorem representedEdge_not_mem_of_avoids {C : Set L.LV}
    (hav : L.lambda.Avoids p C) {e : V × V}
    (he : e ∈ L.representedEdges p) : e ∉ L.edgePart C :=
  Set.disjoint_left.1 (L.avoids_edgePart p hav) he

/-! ## Source and target endpoints -/

/-- A finite auxiliary path beginning in the auxiliary source begins either
at a recorded finite terminal or at one of the fresh ray proxies. -/
theorem start_of_mem_lambda_source (hstart : p.start ∈ L.lambda.source) :
    (∃ x ∈ L.finiteSource, p.start = .old x) ∨
      ∃ i : I, p.start = .proxy i := by
  cases h : p.start with
  | old x =>
      exact Or.inl ⟨x, (L.mem_lambda_source_old x).1 (h ▸ hstart), rfl⟩
  | edge u v =>
      exact False.elim (L.not_mem_lambda_source_edge u v (h ▸ hstart))
  | proxy i => exact Or.inr ⟨i, rfl⟩

/-- A finite auxiliary path ending in the auxiliary target ends at an old
target marker. -/
theorem finish_of_mem_lambda_target (hfinish : p.finish ∈ L.lambda.target) :
    ∃ y ∈ L.targetMarkers, p.finish = .old y := by
  cases h : p.finish with
  | old y => exact ⟨y, (L.mem_lambda_target_old y).1 (h ▸ hfinish), rfl⟩
  | edge u v =>
      exact False.elim (L.not_mem_lambda_target_edge u v (h ▸ hfinish))
  | proxy i =>
      exact False.elim (L.not_mem_lambda_target_proxy i (h ▸ hfinish))

/-- Every old start has the expected original entry and exit. -/
theorem start_old_gadget {x : V} (h : p.start = .old x) :
    L.gadgetEntry p.start = some x ∧ L.gadgetExit p.start = some x := by
  rw [h]
  exact ⟨rfl, rfl⟩

/-- Every old target finish has the expected original entry and exit. -/
theorem finish_old_gadget {y : V} (h : p.finish = .old y) :
    L.gadgetEntry p.finish = some y ∧ L.gadgetExit p.finish = some y := by
  rw [h]
  exact ⟨rfl, rfl⟩

end Input
end PopularAuxiliary
end Erdos599
