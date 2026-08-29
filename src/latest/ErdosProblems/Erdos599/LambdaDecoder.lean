/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaAlternating

/-!
# The finite path decoder for the Section 8 auxiliary web

A vertex of `Input.lambda` which represents an edge `u -> v` contributes
that edge with *backward* traversal, from `v` to `u`.  An arc of the
auxiliary path contributes either one forward edge of the original graph or
no edge at all (the latter is the equality join between consecutive
backward edges).  This file records these contributions in their actual
order along a finite auxiliary path.

The resulting `MicroTrace` is the lossless layer below maximal-link
compression.  In particular it records direction, traversal endpoints,
continuity, graph validity, the ladder membership of every backward edge,
and the exact edge set `decodedRouteEdges`.  The last section gives the
switch-realization API: any alternating compression with this edge set has
exactly the decoded switching data.
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

/-! ## Signed original edges -/

/-- One edge of the decoded route, retaining the direction in which the
alternating route traverses it.  The stored ordered pair always has the
orientation of the original digraph. -/
structure SignedEdge (V : Type u) where
  edge : V × V
  direction : Direction
  deriving DecidableEq

namespace SignedEdge

/-- A forward edge is traversed in its graph orientation, while a backward
edge is traversed against its graph orientation. -/
def entry (s : SignedEdge V) : V :=
  match s.direction with
  | .forward => s.edge.1
  | .backward => s.edge.2

def exit (s : SignedEdge V) : V :=
  match s.direction with
  | .forward => s.edge.2
  | .backward => s.edge.1

def forward (e : V × V) : SignedEdge V := ⟨e, .forward⟩

def backward (e : V × V) : SignedEdge V := ⟨e, .backward⟩

@[simp] theorem edge_forward (e : V × V) : (forward e).edge = e := rfl
@[simp] theorem direction_forward (e : V × V) :
    (forward e).direction = .forward := rfl
@[simp] theorem entry_forward (e : V × V) : (forward e).entry = e.1 := rfl
@[simp] theorem exit_forward (e : V × V) : (forward e).exit = e.2 := rfl

@[simp] theorem edge_backward (e : V × V) : (backward e).edge = e := rfl
@[simp] theorem direction_backward (e : V × V) :
    (backward e).direction = .backward := rfl
@[simp] theorem entry_backward (e : V × V) : (backward e).entry = e.2 := rfl
@[simp] theorem exit_backward (e : V × V) : (backward e).exit = e.1 := rfl

/-- Every signed edge is a genuine edge of the original graph. -/
def Valid (s : SignedEdge V) : Prop :=
  Gamma.graph.Adj s.edge.1 s.edge.2

end SignedEdge

/-! ## The deterministic expansion of a Lambda walk -/

/-- The contribution of a gadget.  Ordinary vertices and proxies contribute
no edge.  An edge gadget contributes the represented edge backwards. -/
def gadgetSteps : L.LV -> List (SignedEdge V)
  | .old _ => []
  | .edge x y => [SignedEdge.backward (x, y)]
  | .proxy _ => []

/-- The selected contribution of an auxiliary arc.  Backward equality
joins contribute no edge. -/
def connectorSteps (a b : L.LV) : List (SignedEdge V) :=
  match L.chosenConnector? a b with
  | some e => [SignedEdge.forward e]
  | none => []

/-- Expand a Lambda walk in traversal order.  Each gadget is expanded once,
including both endpoint gadgets; between them comes the selected expansion
of the corresponding auxiliary arc. -/
def decodeWalkSteps : {a b : L.LV} -> Walk L.lambda.graph a b ->
    List (SignedEdge V)
  | a, _, .nil => L.gadgetSteps a
  | _, _, @Walk.cons _ _ a b c h q =>
      L.gadgetSteps a ++ L.connectorSteps a b ++ decodeWalkSteps q

@[simp] theorem decodeWalkSteps_nil (a : L.LV) :
    L.decodeWalkSteps (Walk.nil : Walk L.lambda.graph a a) =
      L.gadgetSteps a := rfl

@[simp] theorem decodeWalkSteps_cons {a b c : L.LV}
    (h : L.lambda.graph.Adj a b) (q : Walk L.lambda.graph b c) :
    L.decodeWalkSteps (Walk.cons h q) =
      L.gadgetSteps a ++ L.connectorSteps a b ++ L.decodeWalkSteps q := rfl

/-- The unoriented edge set carried by a list of signed edges. -/
def signedEdgeSet (q : List (SignedEdge V)) : Set (V × V) :=
  {e | exists s, s ∈ q ∧ s.edge = e}

/-- Edges carried with a specified traversal direction. -/
def directedSignedEdgeSet (d : Direction) (q : List (SignedEdge V)) :
    Set (V × V) :=
  {e | exists s, s ∈ q ∧ s.direction = d ∧ s.edge = e}

@[simp] theorem signedEdgeSet_nil :
    signedEdgeSet ([] : List (SignedEdge V)) = ∅ := by
  ext e
  simp [signedEdgeSet, eq_comm]

@[simp] theorem signedEdgeSet_cons (s : SignedEdge V)
    (q : List (SignedEdge V)) :
    signedEdgeSet (s :: q) = {s.edge} ∪ signedEdgeSet q := by
  ext e
  simp only [signedEdgeSet, Set.mem_setOf_eq, List.mem_cons,
    Set.mem_union, Set.mem_singleton_iff]
  aesop

@[simp] theorem signedEdgeSet_append (q r : List (SignedEdge V)) :
    signedEdgeSet (q ++ r) = signedEdgeSet q ∪ signedEdgeSet r := by
  ext e
  simp only [signedEdgeSet, Set.mem_setOf_eq, List.mem_append, Set.mem_union]
  aesop

@[simp] theorem directedSignedEdgeSet_nil (d : Direction) :
    directedSignedEdgeSet d ([] : List (SignedEdge V)) = ∅ := by
  ext e
  simp [directedSignedEdgeSet]

@[simp] theorem directedSignedEdgeSet_cons (d : Direction)
    (s : SignedEdge V) (q : List (SignedEdge V)) :
    directedSignedEdgeSet d (s :: q) =
      (if s.direction = d then {s.edge} else ∅) ∪
        directedSignedEdgeSet d q := by
  ext e
  simp only [directedSignedEdgeSet, Set.mem_setOf_eq, List.mem_cons,
    Set.mem_union]
  by_cases hsd : s.direction = d <;> simp only [hsd, ↓reduceIte,
    Set.mem_singleton_iff, Set.mem_empty_iff_false, false_or]
  all_goals aesop

@[simp] theorem directedSignedEdgeSet_append (d : Direction)
    (q r : List (SignedEdge V)) :
    directedSignedEdgeSet d (q ++ r) =
      directedSignedEdgeSet d q ∪ directedSignedEdgeSet d r := by
  ext e
  simp only [directedSignedEdgeSet, Set.mem_setOf_eq, List.mem_append,
    Set.mem_union]
  aesop

@[simp] theorem signedEdgeSet_eq_direction_union (q : List (SignedEdge V)) :
    signedEdgeSet q =
      directedSignedEdgeSet .backward q ∪ directedSignedEdgeSet .forward q := by
  ext e
  constructor
  · rintro ⟨s, hs, rfl⟩
    cases h : s.direction with
    | forward => exact Or.inr ⟨s, hs, h, rfl⟩
    | backward => exact Or.inl ⟨s, hs, h, rfl⟩
  · rintro (⟨s, hs, _hd, rfl⟩ | ⟨s, hs, _hd, rfl⟩) <;>
      exact ⟨s, hs, rfl⟩

@[simp] theorem backwardEdges_gadgetSteps (a : L.LV) :
    directedSignedEdgeSet .backward (L.gadgetSteps a) =
      {e | a = .edge e.1 e.2} := by
  cases a with
  | old x => simp [gadgetSteps, directedSignedEdgeSet]
  | edge x y =>
      ext e
      simp [gadgetSteps, directedSignedEdgeSet, SignedEdge.backward,
        Prod.ext_iff, eq_comm]
  | proxy i => simp [gadgetSteps, directedSignedEdgeSet]

@[simp] theorem forwardEdges_gadgetSteps (a : L.LV) :
    directedSignedEdgeSet .forward (L.gadgetSteps a) = ∅ := by
  cases a <;> simp [gadgetSteps, directedSignedEdgeSet, SignedEdge.backward]

@[simp] theorem backwardEdges_connectorSteps (a b : L.LV) :
    directedSignedEdgeSet .backward (L.connectorSteps a b) = ∅ := by
  classical
  simp only [connectorSteps]
  split <;> simp [directedSignedEdgeSet, SignedEdge.forward]

@[simp] theorem forwardEdges_connectorSteps (a b : L.LV) :
    directedSignedEdgeSet .forward (L.connectorSteps a b) =
      {e | L.chosenConnector? a b = some e} := by
  classical
  simp only [connectorSteps]
  split
  next e he =>
    ext f
    simp [directedSignedEdgeSet, SignedEdge.forward, he]
  next he =>
    ext f
    simp [directedSignedEdgeSet, he]

/-! ## Exact edge accounting -/

/-- Backward signed edges are exactly the edge gadgets visited by the walk.
The family-membership conjunct in `representedEdges` is added below using
the source hypothesis. -/
theorem backwardEdges_decodeWalkSteps {a b : L.LV}
    (q : Walk L.lambda.graph a b) :
    directedSignedEdgeSet .backward (L.decodeWalkSteps q) =
      {e | LambdaVertex.edge e.1 e.2 ∈ q.support} := by
  induction q with
  | nil =>
      ext e
      simp [decodeWalkSteps, Walk.support, eq_comm]
  | @cons a b c h q ih =>
      simp only [decodeWalkSteps_cons, directedSignedEdgeSet_append,
        backwardEdges_gadgetSteps, backwardEdges_connectorSteps,
        Set.union_empty, ih, Walk.support_cons, List.mem_cons]
      ext e
      simp [eq_comm]

/-- Forward signed edges are exactly the selected connectors of the walk. -/
theorem forwardEdges_decodeWalkSteps {a b : L.LV}
    (q : Walk L.lambda.graph a b) :
    directedSignedEdgeSet .forward (L.decodeWalkSteps q) =
      {e | exists x y, (x, y) ∈ q.edgeSet ∧
        L.chosenConnector? x y = some e} := by
  induction q with
  | nil =>
      simp [decodeWalkSteps, Walk.edgeSet]
  | @cons a b c h q ih =>
      simp only [decodeWalkSteps_cons, directedSignedEdgeSet_append,
        forwardEdges_gadgetSteps, forwardEdges_connectorSteps,
        Set.empty_union, ih, Walk.edgeSet_cons]
      ext e
      constructor
      · rintro (he | ⟨x, y, hxy, he⟩)
        · refine ⟨a, b, ?_, he⟩
          exact Or.inl (Set.mem_singleton (a, b))
        · exact ⟨x, y, Or.inr hxy, he⟩
      · rintro ⟨x, y, hxy | hxy, he⟩
        · rcases hxy with ⟨rfl, rfl⟩
          exact Or.inl he
        · exact Or.inr ⟨x, y, hxy, he⟩

/-- The signed expansion has precisely `decodedRouteEdges` as its edge set.
This is the central losslessness theorem of the decoder. -/
theorem signedEdgeSet_decodeWalkSteps
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source) :
    signedEdgeSet (L.decodeWalkSteps p.walk) = L.decodedRouteEdges p := by
  rw [signedEdgeSet_eq_direction_union,
    L.backwardEdges_decodeWalkSteps p.walk,
    L.forwardEdges_decodeWalkSteps p.walk]
  ext e
  constructor
  · rintro (he | he)
    · exact Or.inl ⟨he,
        L.edgeNode_mem_familyEdges_of_start_in_source p hstart he⟩
    · rcases he with ⟨a, b, hab, hchosen⟩
      exact Or.inr ⟨a, b, hab, hchosen⟩
  · rintro (he | he)
    · exact Or.inl he.1
    · rcases he with ⟨a, b, hab, hchosen⟩
      exact Or.inr ⟨a, b, hab, hchosen⟩

/-! ## Ordered traversal -/

/-- A list of signed edges is traversable from `x` to `y` when the entry of
its first edge is `x`, consecutive traversal endpoints agree, and the last
exit is `y`.  The empty trace is allowed exactly when its endpoints agree. -/
inductive RunsFromTo : V -> V -> List (SignedEdge V) -> Prop
  | nil (x : V) : RunsFromTo x x []
  | cons (s : SignedEdge V) {z : V} {q : List (SignedEdge V)}
      (tail : RunsFromTo s.exit z q) : RunsFromTo s.entry z (s :: q)

namespace RunsFromTo

theorem append {x y z : V} {q r : List (SignedEdge V)}
    (hq : RunsFromTo x y q) (hr : RunsFromTo y z r) :
    RunsFromTo x z (q ++ r) := by
  induction hq with
  | nil => simpa using hr
  | cons s tail ih =>
      exact .cons s (ih hr)

theorem singleton (s : SignedEdge V) :
    RunsFromTo s.entry s.exit [s] := by
  exact .cons s (.nil s.exit)

theorem start_eq_of_nil {x y : V} (h : RunsFromTo x y []) : x = y := by
  cases h
  rfl

theorem nonempty_of_ne {x y : V} {q : List (SignedEdge V)}
    (h : RunsFromTo x y q) (hxy : x ≠ y) : q ≠ [] := by
  intro hnil
  subst q
  exact hxy h.start_eq_of_nil

end RunsFromTo

/-- Traversing the contribution of a non-proxy gadget goes from its entry
to its exit. -/
theorem gadgetSteps_runs {a : L.LV} {x y : V}
    (hentry : L.gadgetEntry a = some x)
    (hexit : L.gadgetExit a = some y) :
    RunsFromTo x y (L.gadgetSteps a) := by
  cases a with
  | old z =>
      simp only [gadgetEntry_old, Option.some.injEq] at hentry
      simp only [gadgetExit_old, Option.some.injEq] at hexit
      subst x
      subst y
      exact .nil z
  | edge u w =>
      simp only [gadgetEntry_edge, Option.some.injEq] at hentry
      simp only [gadgetExit_edge, Option.some.injEq] at hexit
      subst x
      subst y
      exact RunsFromTo.singleton (SignedEdge.backward (u, w))
  | proxy i => simp at hentry

/-- A selected forward connector is a one-edge traversal from the exit of
its left gadget (or a selected point of an initial proxy) to the entry of
its right gadget. -/
theorem connectorSteps_runs_of_some {a b : L.LV} {x y : V}
    (hchosen : L.chosenConnector? a b = some (x, y)) :
    RunsFromTo x y (L.connectorSteps a b) := by
  simp [connectorSteps, hchosen]
  exact RunsFromTo.singleton (SignedEdge.forward (x, y))

/-- A backward join contributes no signed edge and identifies the two
adjacent gadget endpoints. -/
theorem connectorSteps_runs_of_none {a b : L.LV} {x : V}
    (hchosen : L.chosenConnector? a b = none) :
    RunsFromTo x x (L.connectorSteps a b) := by
  simp [connectorSteps, hchosen]
  exact .nil x

/-- Every gadget with an entry also has an exit. -/
theorem exists_gadgetExit_of_entry {a : L.LV} {x : V}
    (hentry : L.gadgetEntry a = some x) :
    ∃ y, L.gadgetExit a = some y := by
  cases a with
  | old y => exact ⟨y, rfl⟩
  | edge y z => exact ⟨y, rfl⟩
  | proxy i => simp at hentry

/-- Decode a suffix whose initial gadget has an ordinary entry. -/
theorem decodeWalkSteps_runs_from_entry {a b : L.LV}
    (q : Walk L.lambda.graph a b) {x z : V}
    (hentry : L.gadgetEntry a = some x)
    (hexit : L.gadgetExit b = some z) :
    RunsFromTo x z (L.decodeWalkSteps q) := by
  induction q generalizing x with
  | nil =>
      exact L.gadgetSteps_runs hentry hexit
  | @cons a b c hab q ih =>
      obtain ⟨r, haexit⟩ := L.exists_gadgetExit_of_entry hentry
      have hleft : RunsFromTo x r (L.gadgetSteps a) :=
        L.gadgetSteps_runs hentry haexit
      cases hopt : L.chosenConnector? a b with
      | some e =>
          rcases e with ⟨s, t⟩
          have hconn := L.chosenConnector?_eq_some hopt
          have hnotproxy : ¬ ∃ i : I,
              a = .proxy i ∧ s ∈ (L.proxyPath i).support := by
            rintro ⟨i, rfl, _⟩
            simp at hentry
          have hsexit : L.gadgetExit a = some s :=
            Or.resolve_right hconn.1 hnotproxy
          have hsr : s = r := Option.some.inj (hsexit.symm.trans haexit)
          subst s
          have hbentry : L.gadgetEntry b = some t := hconn.2.1
          exact (hleft.append
            (L.connectorSteps_runs_of_some hopt)).append (ih hbentry hexit)
      | none =>
          have hjoin := L.chosenConnector?_eq_none_of_adj hab hopt
          obtain ⟨m, hExitA, hEntryB⟩ := hjoin.exit_eq_entry
          have hmr : m = r := Option.some.inj (hExitA.symm.trans haexit)
          subst m
          exact (hleft.append
            (L.connectorSteps_runs_of_none hopt)).append (ih hEntryB hexit)

/-- Decode a Lambda walk starting at a proxy.  Its first auxiliary arc is
necessarily a selected forward connector whose initial endpoint lies on the
represented ray. -/
theorem decodeWalkSteps_runs_from_proxy {i : I} {b : L.LV}
    (q : Walk L.lambda.graph (.proxy i) b) {z : V}
    (hexit : L.gadgetExit b = some z) :
    exists x, x ∈ (L.proxyPath i).support ∧
      RunsFromTo x z (L.decodeWalkSteps q) := by
  cases q with
  | nil => simp at hexit
  | @cons _ c b h q =>
      cases hopt : L.chosenConnector? (.proxy i) c with
      | none =>
          have hjoin := L.chosenConnector?_eq_none_of_adj h hopt
          rcases hjoin with hjoin | hjoin | hjoin
          · rcases hjoin with ⟨u, v, hproxy, _hc, _huv, _hu⟩
            simp at hproxy
          · rcases hjoin with ⟨u, v, hproxy, _hc, _huv, _hv⟩
            simp at hproxy
          · rcases hjoin with ⟨u, v, w, hproxy, _hc, _huv, _hwu⟩
            simp at hproxy
      | some e =>
          rcases e with ⟨x, y⟩
          have hconn := L.chosenConnector?_eq_some hopt
          have hx : x ∈ (L.proxyPath i).support := by
            rcases hconn.1 with hbad | hproxy
            · simp at hbad
            · rcases hproxy with ⟨j, hji, hx⟩
              simp at hji
              subst j
              exact hx
          have hcentry : L.gadgetEntry c = some y := hconn.2.1
          refine ⟨x, hx, ?_⟩
          simp only [decodeWalkSteps_cons, gadgetSteps, List.nil_append]
          exact (L.connectorSteps_runs_of_some hopt).append
            (L.decodeWalkSteps_runs_from_entry q hcentry hexit)

/-- Equality-transported form used for a dependent path whose start is
known to be a proxy. -/
theorem decodeWalkSteps_runs_from_eq_proxy {a b : L.LV} {i : I}
    (q : Walk L.lambda.graph a b) (ha : a = .proxy i) {z : V}
    (hexit : L.gadgetExit b = some z) :
    ∃ x, x ∈ (L.proxyPath i).support ∧
      RunsFromTo x z (L.decodeWalkSteps q) := by
  subst a
  exact L.decodeWalkSteps_runs_from_proxy q hexit

/-! ## The certified finite decoder -/

/-- A lossless finite signed route in the original graph. -/
structure MicroTrace (p : FinitePath L.lambda.graph) where
  steps : List (SignedEdge V)
  initial : V
  terminal : V
  runs : RunsFromTo initial terminal steps
  edgeSet_eq : signedEdgeSet steps = L.decodedRouteEdges p
  valid : forall s, s ∈ steps -> SignedEdge.Valid (Gamma := Gamma) s
  backward_on_ladder : forall s, s ∈ steps -> s.direction = .backward ->
    s.edge ∈ L.familyEdges
  source_endpoint :
    (∃ x ∈ L.finiteSource, initial = x) ∨
      ∃ i : I, initial ∈ (L.proxyPath i).support
  target_endpoint : terminal ∈ L.targetMarkers

/-- All steps in the deterministic expansion are genuine original edges. -/
theorem decodeWalkSteps_valid (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source) {s : SignedEdge V}
    (hs : s ∈ L.decodeWalkSteps p.walk) :
    SignedEdge.Valid (Gamma := Gamma) s := by
  have hedge : s.edge ∈ L.decodedRouteEdges p := by
    rw [<- L.signedEdgeSet_decodeWalkSteps p hstart]
    exact ⟨s, hs, rfl⟩
  exact L.decodedRouteEdges_subset_adj p hedge

/-- A backward step in the deterministic expansion comes from an edge
gadget, hence from the limiting ladder warp. -/
theorem decodeWalkSteps_backward_on_ladder
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source) {s : SignedEdge V}
    (hs : s ∈ L.decodeWalkSteps p.walk)
    (hback : s.direction = .backward) :
    s.edge ∈ L.familyEdges := by
  have hedge : s.edge ∈ directedSignedEdgeSet .backward
      (L.decodeWalkSteps p.walk) := ⟨s, hs, hback, rfl⟩
  rw [L.backwardEdges_decodeWalkSteps p.walk] at hedge
  exact L.edgeNode_mem_familyEdges_of_start_in_source p hstart hedge

/-- A type-valued source-endpoint witness, used to avoid eliminating a
propositional existential while constructing the decoded trace. -/
abbrev SourceEndpointChoice (p : FinitePath L.lambda.graph) :=
  Sum {x : V // x ∈ L.finiteSource ∧ p.start = .old x}
    {i : I // p.start = .proxy i}

noncomputable def chooseSourceEndpoint
    (p : FinitePath L.lambda.graph) (hstart : p.start ∈ L.lambda.source) :
    L.SourceEndpointChoice p :=
  Classical.choice (by
    rcases L.start_of_mem_lambda_source p hstart with
        ⟨x, hx, hpx⟩ | ⟨i, hpi⟩
    · exact ⟨Sum.inl ⟨x, hx, hpx⟩⟩
    · exact ⟨Sum.inr ⟨i, hpi⟩⟩)

/-- A type-valued target-endpoint witness for the same reason. -/
noncomputable def chooseTargetEndpoint
    (p : FinitePath L.lambda.graph) (hfinish : p.finish ∈ L.lambda.target) :
    {y : V // y ∈ L.targetMarkers ∧ p.finish = .old y} :=
  Classical.choice (by
    rcases L.finish_of_mem_lambda_target p hfinish with ⟨y, hy, hpy⟩
    exact ⟨⟨y, hy, hpy⟩⟩)

/-- Build the decoded trace when the auxiliary source is an old finite
terminal. -/
noncomputable def decodeFinitePathFromFinite
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (x : {x : V // x ∈ L.finiteSource ∧ p.start = .old x})
    (y : {y : V // y ∈ L.targetMarkers ∧ p.finish = .old y}) :
    L.MicroTrace p := by
  have hyTarget : y.1 ∈ L.targetMarkers := y.2.1
  have hpy : p.finish = .old y.1 := y.2.2
  have hfinishExit : L.gadgetExit p.finish = some y :=
    (L.finish_old_gadget p hpy).2
  have hxSource : x.1 ∈ L.finiteSource := x.2.1
  have hpx : p.start = .old x.1 := x.2.2
  have hstartEntry : L.gadgetEntry p.start = some x.1 :=
    (L.start_old_gadget p hpx).1
  exact {
    steps := L.decodeWalkSteps p.walk
    initial := x.1
    terminal := y.1
    runs := L.decodeWalkSteps_runs_from_entry p.walk hstartEntry hfinishExit
    edgeSet_eq := L.signedEdgeSet_decodeWalkSteps p hstart
    valid := fun _ hs => L.decodeWalkSteps_valid p hstart hs
    backward_on_ladder := fun _ hs hb =>
      L.decodeWalkSteps_backward_on_ladder p hstart hs hb
    source_endpoint := Or.inl ⟨x.1, hxSource, rfl⟩
    target_endpoint := hyTarget }

/-- Build the decoded trace when the auxiliary source is a proxy for a
recorded ray. -/
noncomputable def decodeFinitePathFromProxy
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (i : {i : I // p.start = .proxy i})
    (y : {y : V // y ∈ L.targetMarkers ∧ p.finish = .old y}) :
    L.MicroTrace p := by
  have hfinishExit : L.gadgetExit p.finish = some y.1 :=
    (L.finish_old_gadget p y.2.2).2
  let xr : {x : V // x ∈ (L.proxyPath i.1).support ∧
      RunsFromTo x y.1 (L.decodeWalkSteps p.walk)} :=
    Classical.choice (by
      rcases L.decodeWalkSteps_runs_from_eq_proxy p.walk i.2 hfinishExit with
        ⟨x, hxRay, hrun⟩
      exact ⟨⟨x, hxRay, hrun⟩⟩)
  exact {
    steps := L.decodeWalkSteps p.walk
    initial := xr.1
    terminal := y.1
    runs := xr.2.2
    edgeSet_eq := L.signedEdgeSet_decodeWalkSteps p hstart
    valid := fun _ hs => L.decodeWalkSteps_valid p hstart hs
    backward_on_ladder := fun _ hs hb =>
      L.decodeWalkSteps_backward_on_ladder p hstart hs hb
    source_endpoint := Or.inr ⟨i.1, xr.2.1⟩
    target_endpoint := y.2.1 }

/-- The genuine finite Lambda-path decoder. -/
noncomputable def decodeFinitePath
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (hfinish : p.finish ∈ L.lambda.target) : L.MicroTrace p :=
  match L.chooseSourceEndpoint p hstart with
  | .inl x => L.decodeFinitePathFromFinite p hstart x
      (L.chooseTargetEndpoint p hfinish)
  | .inr i => L.decodeFinitePathFromProxy p hstart i
      (L.chooseTargetEndpoint p hfinish)

@[simp] theorem decodeFinitePath_steps
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (hfinish : p.finish ∈ L.lambda.target) :
  (L.decodeFinitePath p hstart hfinish).steps =
      L.decodeWalkSteps p.walk := by
  classical
  unfold decodeFinitePath
  cases L.chooseSourceEndpoint p hstart <;> rfl

theorem decodeFinitePath_edgeSet
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (hfinish : p.finish ∈ L.lambda.target) :
    signedEdgeSet (L.decodeFinitePath p hstart hfinish).steps =
      L.decodedRouteEdges p :=
  (L.decodeFinitePath p hstart hfinish).edgeSet_eq

/-! ## Maximal-link compression and switching -/

/-- An alternating compression of a decoded micro-trace.  The combinatorial
compression is deliberately separated from the lossless Lambda decoder: it
may coalesce consecutive signed edges in either direction into maximal
links, but it must retain the ordered endpoints and the exact edge set. -/
structure AlternatingCompression (p : FinitePath L.lambda.graph)
    (T : L.MicroTrace p) where
  path : AltPath Gamma.graph
  edgeSet_eq : path.edgeSet = signedEdgeSet T.steps
  initial_eq : path.initial = T.initial
  terminal_eq : path.terminal? = some T.terminal

/-- Every alternating compression has precisely the decoded route edge
set. -/
theorem AlternatingCompression.edgeSet_eq_decodedRouteEdges
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (C : L.AlternatingCompression p T) :
    C.path.edgeSet = L.decodedRouteEdges p :=
  C.edgeSet_eq.trans T.edgeSet_eq

/-- Hence a compressed decoder path induces exactly the selected raw
switching data. -/
theorem AlternatingCompression.switchData_eq
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (C : L.AlternatingCompression p T) :
    L.decodedSwitchData p =
      Alternating.Cyclowarp.application L.ladder.paths C.path :=
  L.decodedSwitchData_eq_application_of_edgeSet p C.path
    C.edgeSet_eq_decodedRouteEdges

/-- Switching realizations transport directly across a compression. -/
theorem AlternatingCompression.realizedBy
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (C : L.AlternatingCompression p T) (W : Set Gamma.DPath)
    (hW : (Alternating.Cyclowarp.application L.ladder.paths C.path).RealizedBy W) :
    (L.decodedSwitchData p).RealizedBy W := by
  rw [C.switchData_eq]
  exact hW

/-- The source endpoint of a compression is either a recorded finite source
or a point of the ray represented by its initial proxy. -/
theorem AlternatingCompression.source_endpoint
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (C : L.AlternatingCompression p T) :
    (∃ x ∈ L.finiteSource, C.path.initial = x) ∨
      ∃ i : I, C.path.initial ∈ (L.proxyPath i).support := by
  simpa only [C.initial_eq] using T.source_endpoint

/-- The terminal of a compression is the decoded target marker. -/
theorem AlternatingCompression.target_endpoint
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (C : L.AlternatingCompression p T) :
    ∃ y ∈ L.targetMarkers, C.path.terminal? = some y :=
  ⟨T.terminal, T.target_endpoint, C.terminal_eq⟩

end Input
end PopularAuxiliary
end Erdos599
