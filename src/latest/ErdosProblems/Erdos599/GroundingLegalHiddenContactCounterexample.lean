/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteSourceDuplicateExchange
import ErdosProblems.Erdos599.TerminalContactSwitch

/-!
# A legal-compatible hidden contact after chronological erasure

The signed route

`c <- r -> x <- u -> v <- x -> y`

has a simple Lambda realization.  Chronological erasure removes the closed
interval `x <- u -> v <- x`, leaving `c <- r -> x -> y`.  The retained
forward run meets the ladder at the internal vertex `x`, while the backward
link that formerly covered `x` has disappeared.  Unlike the smaller overlap
example, the finite source is `c`, the target marker is `y`, and the grounded
record ending at `c` is disjoint from `y`.

This module proves the exact obstruction on the erased two-link trace.  In
particular, the first uncovered contact `x` is neither an initial vertex nor
an isolated component of the reference warp, so the isolated-terminal
normalization constructor cannot close this case.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingLegalHiddenContactCounterexample

open DirectedPath Alternating

inductive Vertex
  | r | c | u | x | v | y
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj p q :=
    (p = r ∧ q = c) ∨ (p = r ∧ q = x) ∨
    (p = u ∧ q = x) ∨ (p = u ∧ q = v) ∨
    (p = x ∧ q = v) ∨ (p = x ∧ q = y)

@[simp] theorem graph_adj (p q : Vertex) :
    graph.Adj p q ↔
      (p = r ∧ q = c) ∨ (p = r ∧ q = x) ∨
      (p = u ∧ q = x) ∨ (p = u ∧ q = v) ∨
      (p = x ∧ q = v) ∨ (p = x ∧ q = y) :=
  Iff.rfl

def rc : FinitePath graph where
  start := r
  finish := c
  walk := .cons (by simp [graph]) .nil
  isPath := by
    change [r, c].Nodup
    simp

def uxv : FinitePath graph where
  start := u
  finish := v
  walk := .cons (v := x) (by simp [graph])
    (.cons (by simp [graph]) .nil)
  isPath := by
    change [u, x, v].Nodup
    simp

def rxy : FinitePath graph where
  start := r
  finish := y
  walk := .cons (v := x) (by simp [graph])
    (.cons (by simp [graph]) .nil)
  isPath := by
    change [r, x, y].Nodup
    simp

def rx : FinitePath graph where
  start := r
  finish := x
  walk := .cons (by simp [graph]) .nil
  isPath := by
    change [r, x].Nodup
    simp

def ux : FinitePath graph where
  start := u
  finish := x
  walk := .cons (by simp [graph]) .nil
  isPath := by
    change [u, x].Nodup
    simp

@[simp] theorem rc_start : rc.start = r := rfl
@[simp] theorem rc_finish : rc.finish = c := rfl
@[simp] theorem uxv_start : uxv.start = u := rfl
@[simp] theorem uxv_finish : uxv.finish = v := rfl
@[simp] theorem rxy_start : rxy.start = r := rfl
@[simp] theorem rxy_finish : rxy.finish = y := rfl
@[simp] theorem rx_start : rx.start = r := rfl
@[simp] theorem rx_finish : rx.finish = x := rfl
@[simp] theorem ux_start : ux.start = u := rfl
@[simp] theorem ux_finish : ux.finish = x := rfl

@[simp] theorem rc_support : rc.support = ({r, c} : Set Vertex) := by
  ext z
  change z ∈ [r, c] ↔ _
  simp

@[simp] theorem uxv_support : uxv.support = ({u, x, v} : Set Vertex) := by
  ext z
  change z ∈ [u, x, v] ↔ _
  simp

@[simp] theorem rxy_support : rxy.support = ({r, x, y} : Set Vertex) := by
  ext z
  change z ∈ [r, x, y] ↔ _
  simp

@[simp] theorem rx_support : rx.support = ({r, x} : Set Vertex) := by
  ext z
  change z ∈ [r, x] ↔ _
  simp

@[simp] theorem ux_support : ux.support = ({u, x} : Set Vertex) := by
  ext z
  change z ∈ [u, x] ↔ _
  simp

@[simp] theorem rc_edgeSet :
    rc.walk.edgeSet = ({(r, c)} : Set (Vertex × Vertex)) := by
  simp [rc, DirectedPath.Walk.edgeSet]

@[simp] theorem uxv_edgeSet :
    uxv.walk.edgeSet = ({(u, x), (x, v)} : Set (Vertex × Vertex)) := by
  ext e
  simp [uxv, DirectedPath.Walk.edgeSet]
  tauto

@[simp] theorem rx_edgeSet :
    rx.walk.edgeSet = ({(r, x)} : Set (Vertex × Vertex)) := by
  simp [rx, DirectedPath.Walk.edgeSet]

@[simp] theorem ux_edgeSet :
    ux.walk.edgeSet = ({(u, x)} : Set (Vertex × Vertex)) := by
  simp [ux, DirectedPath.Walk.edgeSet]

def web : DWeb Vertex where
  graph := graph
  source := {r, u, y}
  target := {c, v, y}

def yPath : web.DPath := web.trivialPath y

@[simp] theorem rcD_support :
    DirectedPath.Path.support (Sum.inl rc : web.DPath) =
      ({r, c} : Set Vertex) :=
  rc_support

@[simp] theorem uxvD_support :
    DirectedPath.Path.support (Sum.inl uxv : web.DPath) =
      ({u, x, v} : Set Vertex) :=
  uxv_support

@[simp] theorem rcD_terminal :
    web.terminal? (Sum.inl rc : web.DPath) = some c := rfl

@[simp] theorem uxvD_terminal :
    web.terminal? (Sum.inl uxv : web.DPath) = some v := rfl

@[simp] theorem rcD_initial :
    DirectedPath.Path.initial (Sum.inl rc : web.DPath) = r := rfl

@[simp] theorem uxvD_initial :
    DirectedPath.Path.initial (Sum.inl uxv : web.DPath) = u := rfl

def ladderPaths : Set web.DPath :=
  {(Sum.inl rc : web.DPath), (Sum.inl uxv : web.DPath), yPath}

theorem ladderPaths_isWarp : web.IsWarp ladderPaths := by
  intro p hp q hq hpq
  simp only [ladderPaths, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl
  all_goals simp [Function.onFun, yPath] at hpq ⊢

def ladder : web.Warp := ⟨ladderPaths, ladderPaths_isWarp⟩

def input : PopularAuxiliary.Input web Empty where
  ladder := ladder
  groundedRecords := {(Sum.inl rc : web.DPath)}
  finiteSource := {c}
  markerSet := {y}
  proxyPath i := nomatch i
  proxy_isRay i := nomatch i

@[simp] theorem input_ladder_paths : input.ladder.paths = ladderPaths := rfl
@[simp] theorem input_finiteSource : input.finiteSource = {c} := rfl
@[simp] theorem input_markerSet : input.markerSet = {y} := rfl

@[simp] theorem terminalFrontier_ladderPaths :
    web.terminalFrontier ladderPaths = ({c, v, y} : Set Vertex) := by
  ext z
  simp [ladderPaths, yPath, eq_comm]

@[simp] theorem web_essential_terminalFrontier :
    web.essential ({c, v, y} : Set Vertex) = {c, v, y} := by
  apply Set.Subset.antisymm (web.essential_subset _)
  intro z hz
  refine ⟨hz, ?_⟩
  rw [web.not_mem_roof_iff]
  refine ⟨FinitePath.trivial graph z, ⟨rfl, ?_⟩, ?_⟩
  · simpa [web] using hz
  · change Disjoint (FinitePath.trivial graph z).support
      ({c, v, y} \ {z})
    rw [FinitePath.support_trivial]
    exact Set.disjoint_sdiff_right

@[simp] theorem input_essentialLadder : input.essentialLadder = ladderPaths := by
  ext p
  constructor
  · exact fun hp => hp.1
  · intro hp
    simp only [ladderPaths, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · refine ⟨by simp [ladderPaths], c, rfl, ?_⟩
      simp
    · refine ⟨by simp [ladderPaths], v, rfl, ?_⟩
      simp
    · refine ⟨by simp [ladderPaths], y, by simp [yPath], ?_⟩
      simp

@[simp] theorem input_targetMarkers : input.targetMarkers = {y} := by
  ext z
  constructor
  · exact fun hz => hz.1
  · intro hz
    have hzy : z = y := by simpa using hz
    subst z
    refine ⟨by simp, ?_⟩
    refine ⟨yPath, by simp [ladderPaths], ?_⟩
    simp [yPath]

/-- The two legality-sensitive sets are disjoint. -/
theorem finiteSource_disjoint_targetMarkers :
    Disjoint input.finiteSource input.targetMarkers := by
  simp

/-- The grounded finite record also avoids every target marker. -/
theorem groundedRecord_disjoint_targetMarkers :
    Disjoint rc.support input.targetMarkers := by
  simp

@[simp] theorem familyEdges_ladderPaths :
    familyEdges ladderPaths =
      ({(r, c), (u, x), (x, v)} : Set (Vertex × Vertex)) := by
  ext e
  simp only [familyEdges, Set.mem_iUnion, ladderPaths,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, hp, he⟩
    rcases hp with rfl | rfl | rfl
    · change e ∈ rc.walk.edgeSet at he
      rw [rc_edgeSet] at he
      simp_all
    · change e ∈ uxv.walk.edgeSet at he
      rw [uxv_edgeSet] at he
      simp_all
    · change e ∈ (FinitePath.trivial web.graph y).walk.edgeSet at he
      rw [FinitePath.trivial_walk] at he
      simp at he
  · intro he
    rcases he with he | he | he
    · refine ⟨(Sum.inl rc : web.DPath), by simp [ladderPaths], ?_⟩
      change e ∈ rc.walk.edgeSet
      rw [rc_edgeSet]
      exact Set.mem_singleton_iff.2 he
    · refine ⟨(Sum.inl uxv : web.DPath), by simp [ladderPaths], ?_⟩
      change e ∈ uxv.walk.edgeSet
      rw [uxv_edgeSet]
      exact Or.inl he
    · refine ⟨(Sum.inl uxv : web.DPath), by simp [ladderPaths], ?_⟩
      change e ∈ uxv.walk.edgeSet
      rw [uxv_edgeSet]
      exact Or.inr (Set.mem_singleton_iff.2 he)

theorem rc_mem_familyEdges : (r, c) ∈ input.familyEdges := by
  refine ⟨(Sum.inl rc : web.DPath), by simp [ladderPaths], ?_⟩
  change (r, c) ∈ rc.walk.edgeSet
  simp [rc, DirectedPath.Walk.edgeSet]

theorem ux_mem_familyEdges : (u, x) ∈ input.familyEdges := by
  refine ⟨(Sum.inl uxv : web.DPath), by simp [ladderPaths], ?_⟩
  change (u, x) ∈ uxv.walk.edgeSet
  simp [uxv, DirectedPath.Walk.edgeSet]

theorem xv_mem_familyEdges : (x, v) ∈ input.familyEdges := by
  refine ⟨(Sum.inl uxv : web.DPath), by simp [ladderPaths], ?_⟩
  change (x, v) ∈ uxv.walk.edgeSet
  simp [uxv, DirectedPath.Walk.edgeSet]

abbrev LV := PopularAuxiliary.Input.LambdaVertex Vertex Empty

/-- A simple auxiliary path whose signed expansion is the six-step route
displayed in the module header. -/
def exchangePath : FinitePath input.lambda.graph where
  start := .old c
  finish := .old y
  walk := .cons (by
      exact (input.lambda_adj_old_edge c r c).2
        ⟨rc_mem_familyEdges, Or.inl rfl⟩)
    (.cons (by
        exact (input.lambda_adj_edge_edge r c u x).2
          ⟨rc_mem_familyEdges, ux_mem_familyEdges,
            Or.inr (by simp [web, graph])⟩)
      (.cons (by
          exact (input.lambda_adj_edge_edge u x x v).2
            ⟨ux_mem_familyEdges, xv_mem_familyEdges,
              Or.inr (by simp [web, graph])⟩)
        (.cons (by
            exact (input.lambda_adj_edge_old x v y).2
              ⟨xv_mem_familyEdges,
                Or.inr ⟨Or.inr (by simp), by simp [web, graph]⟩⟩)
          .nil)))
  isPath := by
    change [(.old c : LV), .edge r c, .edge u x, .edge x v, .old y].Nodup
    simp

theorem exchangePath_start_source :
    exchangePath.start ∈ input.lambda.source := by
  rw [show exchangePath.start = (.old c : LV) from rfl,
    input.mem_lambda_source_old]
  simp

theorem exchangePath_finish_target :
    exchangePath.finish ∈ input.lambda.target := by
  rw [show exchangePath.finish = (.old y : LV) from rfl,
    input.mem_lambda_target_old]
  simp

private theorem chosenConnector_oldC_edgeRC :
    input.chosenConnector? (.old c) (.edge r c) = none := by
  have hadj : input.lambda.graph.Adj (.old c) (.edge r c) := by
    rw [input.lambda_adj_old_edge]
    exact ⟨rc_mem_familyEdges, Or.inl rfl⟩
  cases hopt : input.chosenConnector? (.old c) (.edge r c) with
  | none => rfl
  | some e =>
      have hconnector := input.chosenConnector?_eq_some hopt
      have hfst : e.1 = c := by
        rcases hconnector.1 with hexit | hproxy
        · exact (Option.some.inj hexit).symm
        · obtain ⟨i, _hi, _⟩ := hproxy
          cases i
      have hsnd : e.2 = c :=
        (Option.some.inj hconnector.2.1).symm
      have he : e = (c, c) := Prod.ext hfst hsnd
      subst e
      have hadjCC : graph.Adj c c := hconnector.2.2
      simp [graph] at hadjCC

private theorem chosenConnector_edgeRC_edgeUX :
    input.chosenConnector? (.edge r c) (.edge u x) = some (r, x) := by
  have hadj : input.lambda.graph.Adj (.edge r c) (.edge u x) := by
    rw [input.lambda_adj_edge_edge]
    exact ⟨rc_mem_familyEdges, ux_mem_familyEdges,
      Or.inr (by simp [web, graph])⟩
  cases hopt : input.chosenConnector? (.edge r c) (.edge u x) with
  | none =>
      have hjoin := input.chosenConnector?_eq_none_of_adj hadj hopt
      simp [PopularAuxiliary.Input.BackwardJoin] at hjoin
  | some e =>
      have hconnector := input.chosenConnector?_eq_some hopt
      have hfst : e.1 = r := by
        rcases hconnector.1 with hexit | hproxy
        · exact (Option.some.inj hexit).symm
        · obtain ⟨i, _hi, _⟩ := hproxy
          cases i
      have hsnd : e.2 = x :=
        (Option.some.inj hconnector.2.1).symm
      have he : e = (r, x) := Prod.ext hfst hsnd
      exact congrArg some he

private theorem chosenConnector_edgeUX_edgeXV :
    input.chosenConnector? (.edge u x) (.edge x v) = some (u, v) := by
  have hadj : input.lambda.graph.Adj (.edge u x) (.edge x v) := by
    rw [input.lambda_adj_edge_edge]
    exact ⟨ux_mem_familyEdges, xv_mem_familyEdges,
      Or.inr (by simp [web, graph])⟩
  cases hopt : input.chosenConnector? (.edge u x) (.edge x v) with
  | none =>
      have hjoin := input.chosenConnector?_eq_none_of_adj hadj hopt
      simp [PopularAuxiliary.Input.BackwardJoin] at hjoin
  | some e =>
      have hconnector := input.chosenConnector?_eq_some hopt
      have hfst : e.1 = u := by
        rcases hconnector.1 with hexit | hproxy
        · exact (Option.some.inj hexit).symm
        · obtain ⟨i, _hi, _⟩ := hproxy
          cases i
      have hsnd : e.2 = v :=
        (Option.some.inj hconnector.2.1).symm
      have he : e = (u, v) := Prod.ext hfst hsnd
      exact congrArg some he

private theorem chosenConnector_edgeXV_oldY :
    input.chosenConnector? (.edge x v) (.old y) = some (x, y) := by
  have hadj : input.lambda.graph.Adj (.edge x v) (.old y) := by
    rw [input.lambda_adj_edge_old]
    exact ⟨xv_mem_familyEdges,
      Or.inr ⟨Or.inr (by simp), by simp [web, graph]⟩⟩
  cases hopt : input.chosenConnector? (.edge x v) (.old y) with
  | none =>
      have hjoin := input.chosenConnector?_eq_none_of_adj hadj hopt
      simp [PopularAuxiliary.Input.BackwardJoin] at hjoin
  | some e =>
      have hconnector := input.chosenConnector?_eq_some hopt
      have hfst : e.1 = x := by
        rcases hconnector.1 with hexit | hproxy
        · exact (Option.some.inj hexit).symm
        · obtain ⟨i, _hi, _⟩ := hproxy
          cases i
      have hsnd : e.2 = y :=
        (Option.some.inj hconnector.2.1).symm
      have he : e = (x, y) := Prod.ext hfst hsnd
      exact congrArg some he

/-- The Lambda decoder really produces the six signed steps advertised in
the header, before loop erasure. -/
theorem decodeWalkSteps_exchangePath :
    input.decodeWalkSteps exchangePath.walk =
      [PopularAuxiliary.Input.SignedEdge.backward (r, c),
       PopularAuxiliary.Input.SignedEdge.forward (r, x),
       PopularAuxiliary.Input.SignedEdge.backward (u, x),
       PopularAuxiliary.Input.SignedEdge.forward (u, v),
       PopularAuxiliary.Input.SignedEdge.backward (x, v),
       PopularAuxiliary.Input.SignedEdge.forward (x, y)] := by
  simp [exchangePath, PopularAuxiliary.Input.decodeWalkSteps,
    PopularAuxiliary.Input.gadgetSteps,
    PopularAuxiliary.Input.connectorSteps,
    chosenConnector_oldC_edgeRC, chosenConnector_edgeRC_edgeUX,
    chosenConnector_edgeUX_edgeXV, chosenConnector_edgeXV_oldY]

def backwardRC : Link graph where
  path := rc
  direction := .backward
  nontrivial := by simp [rc]

def forwardRXY : Link graph where
  path := rxy
  direction := .forward
  nontrivial := by simp [rxy]

private def erasedLink (i : Fin 2) : Link graph :=
  if i.1 = 0 then backwardRC else forwardRXY

@[simp] private theorem erasedLink_zero : erasedLink 0 = backwardRC := by
  simp [erasedLink]

@[simp] private theorem erasedLink_one : erasedLink 1 = forwardRXY := by
  simp [erasedLink]

/-- The maximal-run compression after deleting the closed `x`-loop. -/
def erasedTrace : FiniteTrace graph where
  lastIndex := 1
  link := erasedLink
  joins := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    simp [erasedLink, backwardRC, forwardRXY, Link.exit, Link.entry, rxy]
  alternates := by
    intro i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    simp [backwardRC, forwardRXY]
  compatible := by
    intro i j hij
    have hiVal : i.1 = 0 := by have := i.isLt; omega
    have hjVal : j.1 = 1 := by have := j.isLt; omega
    have hi : i = (0 : Fin 2) := Fin.ext hiVal
    have hj : j = (1 : Fin 2) := Fin.ext hjVal
    subst i
    subst j
    simp only [erasedLink_zero, erasedLink_one]
    simp [CompatibleInOrder, backwardRC, forwardRXY, Link.entry, Link.exit,
      Link.interior, rc_support, rxy_support]

@[simp] theorem erasedTrace_initial : erasedTrace.initial = c := rfl
@[simp] theorem erasedTrace_terminal : erasedTrace.terminal = y := rfl

@[simp] theorem vertexSet_ladderPaths :
    web.vertexSet ladderPaths = ({r, c, u, x, v, y} : Set Vertex) := by
  ext z
  simp [ladderPaths, yPath]
  tauto

@[simp] theorem initialSet_ladderPaths :
    web.initialSet ladderPaths = ({r, u, y} : Set Vertex) := by
  ext z
  simp [ladderPaths, yPath, eq_comm]

theorem x_mem_forwardVertices :
    x ∈ (AltPath.finite erasedTrace).directionVertices .forward := by
  simp only [AltPath.directionVertices, AltPath.links,
    FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
  refine ⟨forwardRXY, ⟨1, rfl⟩, rfl, ?_⟩
  change x ∈ rxy.support
  simp

theorem x_not_mem_backwardVertices :
    x ∉ (AltPath.finite erasedTrace).directionVertices .backward := by
  intro hx
  simp only [AltPath.directionVertices, AltPath.links,
    FiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hx
  rcases hx with ⟨l, ⟨i, rfl⟩, hdir, hvertex⟩
  have hibound : i.1 < 2 := by simpa [erasedTrace] using i.isLt
  have hi : i.1 = 0 ∨ i.1 = 1 := by omega
  rcases hi with hi | hi
  · have hieq : i = (0 : Fin 2) := Fin.ext hi
    subst i
    change x ∈ rc.support at hvertex
    simp at hvertex
  · have hieq : i = (1 : Fin 2) := Fin.ext hi
    subst i
    simp [erasedTrace, erasedLink, forwardRXY] at hdir

/-- Exact failure of the terminal-relaxed contact condition after the
hidden-contact loop is erased. -/
theorem erasedTrace_not_contactsCoveredAtTerminal :
    ¬ PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
      web ladderPaths (.finite erasedTrace) := by
  intro hcovered
  have hxLadder : x ∈ web.vertexSet ladderPaths := by simp
  rcases hcovered x_mem_forwardVertices hxLadder with hxBack | hxTerminal
  · exact x_not_mem_backwardVertices hxBack
  · change some y = some x at hxTerminal
    have : y = x := Option.some.inj hxTerminal
    cases this

/-- The first uncovered contact in this example is internal, not initial. -/
theorem x_not_mem_initialSet : x ∉ web.initialSet ladderPaths := by
  rw [initialSet_ladderPaths]
  simp

/-- Nor is its reference component trivial: `x` belongs to `uxv`. -/
theorem no_trivial_x_component : web.trivialPath x ∉ ladderPaths := by
  intro hx
  simp only [ladderPaths, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx
  · have hs := congrArg DirectedPath.Path.support hx
    rw [web.support_trivialPath, rcD_support] at hs
    have hr : r ∈ ({x} : Set Vertex) := by
      rw [hs]
      simp
    simpa using hr
  · have hs := congrArg DirectedPath.Path.support hx
    rw [web.support_trivialPath, uxvD_support] at hs
    have hu : u ∈ ({x} : Set Vertex) := by
      rw [hs]
      simp
    simpa using hu
  · have hs := congrArg DirectedPath.Path.support hx
    unfold yPath at hs
    rw [web.support_trivialPath, web.support_trivialPath] at hs
    have hy : y ∈ ({x} : Set Vertex) := by
      rw [hs]
      simp
    simpa using hy

/-! ## A contact-normalized prefix

Instead of erasing the closed interval and retaining the later departure
from `x`, stop after the first backward traversal out of `x`.  The resulting
simple trace is `c <- r -> x <- u`.  Its forward contact `x` is now covered
by the retained backward link, and it ends at the initial vertex `u` of that
ladder component. -/

def forwardRX : Link graph where
  path := rx
  direction := .forward
  nontrivial := by simp [rx]

def backwardUX : Link graph where
  path := ux
  direction := .backward
  nontrivial := by simp [ux]

private def normalizedLink (i : Fin 3) : Link graph :=
  if i.1 = 0 then backwardRC
  else if i.1 = 1 then forwardRX
  else backwardUX

@[simp] private theorem normalizedLink_zero :
    normalizedLink 0 = backwardRC := by simp [normalizedLink]

@[simp] private theorem normalizedLink_one :
    normalizedLink 1 = forwardRX := by simp [normalizedLink]

@[simp] private theorem normalizedLink_two :
    normalizedLink 2 = backwardUX := by simp [normalizedLink]

def normalizedTrace : FiniteTrace graph where
  lastIndex := 2
  link := normalizedLink
  joins := by
    intro i
    have hibound : i.1 < 2 := i.isLt
    have hi : i.1 = 0 ∨ i.1 = 1 := by omega
    rcases hi with hi | hi
    · have hieq : i = (0 : Fin 2) := Fin.ext hi
      subst i
      simp [normalizedLink, backwardRC, forwardRX, Link.exit, Link.entry,
        rc, rx]
    · have hieq : i = (1 : Fin 2) := Fin.ext hi
      subst i
      simp [normalizedLink, forwardRX, backwardUX, Link.exit, Link.entry,
        rx, ux]
  alternates := by
    intro i
    have hibound : i.1 < 2 := i.isLt
    have hi : i.1 = 0 ∨ i.1 = 1 := by omega
    rcases hi with hi | hi
    · have hieq : i = (0 : Fin 2) := Fin.ext hi
      subst i
      simp [normalizedLink, backwardRC, forwardRX]
    · have hieq : i = (1 : Fin 2) := Fin.ext hi
      subst i
      simp [normalizedLink, forwardRX, backwardUX]
  compatible := by
    intro i j hij
    have hibound : i.1 < 3 := i.isLt
    have hjbound : j.1 < 3 := j.isLt
    have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by omega
    have hj : j.1 = 0 ∨ j.1 = 1 ∨ j.1 = 2 := by omega
    rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj
    all_goals try omega
    all_goals
      have hieq : i = ⟨i.1, hibound⟩ := rfl
      have hjeq : j = ⟨j.1, hjbound⟩ := rfl
    · have hi0 : i = (0 : Fin 3) := Fin.ext hi
      have hj1 : j = (1 : Fin 3) := Fin.ext hj
      subst i
      subst j
      simp [CompatibleInOrder, normalizedLink, backwardRC, forwardRX,
        Link.entry, Link.exit, Link.interior, rc_support, rx_support]
    · have hi0 : i = (0 : Fin 3) := Fin.ext hi
      have hj2 : j = (2 : Fin 3) := Fin.ext hj
      subst i
      subst j
      simp [CompatibleInOrder, normalizedLink, backwardRC, backwardUX,
        Link.entry, Link.exit, Link.interior, rc_support, ux_support]
    · have hi1 : i = (1 : Fin 3) := Fin.ext hi
      have hj2 : j = (2 : Fin 3) := Fin.ext hj
      subst i
      subst j
      simp [CompatibleInOrder, normalizedLink, forwardRX, backwardUX,
        Link.entry, Link.exit, Link.interior, rx_support, ux_support]
      ext z
      simp
      constructor
      · rintro ⟨hzr | hzx, hzu | hzx'⟩
        · subst z
          cases hzu
        · exact hzx'
        · exact hzx
        · exact hzx
      · intro hzx
        subst z
        exact ⟨Or.inr rfl, Or.inr rfl⟩

@[simp] theorem normalizedTrace_initial : normalizedTrace.initial = c := rfl
@[simp] theorem normalizedTrace_terminal : normalizedTrace.terminal = u := rfl

theorem ux_isSubpathOf_uxv : ux.IsSubpathOf (Sum.inl uxv) := by
  constructor
  · intro z hz
    change z ∈ ux.support at hz
    rw [ux_support] at hz
    change z ∈ uxv.support
    rw [uxv_support]
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
  · intro e he
    change e ∈ ux.walk.edgeSet at he
    rw [ux_edgeSet] at he
    change e ∈ uxv.walk.edgeSet
    rw [uxv_edgeSet]
    exact Or.inl (Set.mem_singleton_iff.1 he)

theorem normalizedTrace_backwardLinksOn :
    BackwardLinksOn ladderPaths (.finite normalizedTrace) := by
  intro l hl hdir
  simp only [AltPath.links, FiniteTrace.links, Set.mem_range] at hl
  obtain ⟨i, rfl⟩ := hl
  have hibound : i.1 < 3 := by simpa [normalizedTrace] using i.isLt
  have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by omega
  rcases hi with hi | hi | hi
  · have hieq : i = (0 : Fin 3) := Fin.ext hi
    subst i
    refine ⟨(Sum.inl rc : web.DPath), by simp [ladderPaths], ?_⟩
    exact FinitePath.isSubpathOf_self rc
  · have hieq : i = (1 : Fin 3) := Fin.ext hi
    subst i
    simp [normalizedTrace, normalizedLink, forwardRX] at hdir
  · have hieq : i = (2 : Fin 3) := Fin.ext hi
    subst i
    exact ⟨(Sum.inl uxv : web.DPath), by simp [ladderPaths],
      ux_isSubpathOf_uxv⟩

theorem normalizedTrace_forwardLinksOff :
    ForwardLinksOff ladderPaths (.finite normalizedTrace) := by
  intro l hl hdir
  simp only [AltPath.links, FiniteTrace.links, Set.mem_range] at hl
  obtain ⟨i, rfl⟩ := hl
  have hibound : i.1 < 3 := by simpa [normalizedTrace] using i.isLt
  have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by omega
  rcases hi with hi | hi | hi
  · have hieq : i = (0 : Fin 3) := Fin.ext hi
    subst i
    simp [normalizedTrace, normalizedLink, backwardRC] at hdir
  · have hieq : i = (1 : Fin 3) := Fin.ext hi
    subst i
    rw [familyEdges_ladderPaths, Set.disjoint_left]
    intro e heRX heLadder
    have heRX' : e = (r, x) := by
      change e ∈ rx.walk.edgeSet at heRX
      rw [rx_edgeSet] at heRX
      exact Set.mem_singleton_iff.1 heRX
    subst e
    simp at heLadder
  · have hieq : i = (2 : Fin 3) := Fin.ext hi
    subst i
    simp [normalizedTrace, normalizedLink, backwardUX] at hdir

theorem normalizedTrace_contactsCoveredAtTerminal :
    PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
      web ladderPaths (.finite normalizedTrace) := by
  intro z hzForward _hzLadder
  have hz : z = r ∨ z = x := by
    simp only [AltPath.directionVertices, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hzForward
    rcases hzForward with ⟨l, ⟨i, rfl⟩, hdir, hzl⟩
    have hibound : i.1 < 3 := by simpa [normalizedTrace] using i.isLt
    have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by omega
    rcases hi with hi | hi | hi
    · have hieq : i = (0 : Fin 3) := Fin.ext hi
      subst i
      simp [normalizedTrace, normalizedLink, backwardRC] at hdir
    · have hieq : i = (1 : Fin 3) := Fin.ext hi
      subst i
      change z ∈ rx.support at hzl
      simpa using hzl
    · have hieq : i = (2 : Fin 3) := Fin.ext hi
      subst i
      simp [normalizedTrace, normalizedLink, backwardUX] at hdir
  left
  simp only [AltPath.directionVertices, AltPath.links,
    FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
  rcases hz with rfl | rfl
  · refine ⟨backwardRC, ⟨0, ?_⟩, rfl, ?_⟩
    · rfl
    · change r ∈ rc.support
      simp
  · refine ⟨backwardUX, ⟨2, ?_⟩, rfl, ?_⟩
    · rfl
    · change x ∈ ux.support
      simp

theorem normalizedTrace_isTerminalRelaxedAlternating :
    PopularAuxiliary.Input.IsTerminalRelaxedAlternating
      web ladderPaths (.finite normalizedTrace) := by
  refine ⟨ladderPaths_isWarp, normalizedTrace_backwardLinksOn,
    normalizedTrace_forwardLinksOff,
    normalizedTrace_contactsCoveredAtTerminal, ?_⟩
  intro hfirst
  change some normalizedTrace.firstLink.direction = some .forward at hfirst
  have hdir : normalizedTrace.firstLink.direction = .forward :=
    Option.some.inj hfirst
  change Direction.backward = Direction.forward at hdir
  cases hdir

theorem normalizedTrace_terminalContactSwitching :
    IsTerminalContactSwitching ladderPaths normalizedTrace u := by
  refine IsTerminalContactSwitching.of_terminalRelaxed
    normalizedTrace_isTerminalRelaxedAlternating rfl ?_ ?_ ?_
  · rw [initialSet_ladderPaths]
    simp
  · exact ⟨x, by rw [familyEdges_ladderPaths]; simp⟩
  · intro hout
    obtain ⟨z, huz⟩ := hout
    simp only [AltPath.directionEdges, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range] at huz
    rcases huz with ⟨l, ⟨i, rfl⟩, hdir, he⟩
    have hibound : i.1 < 3 := by simpa [normalizedTrace] using i.isLt
    have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by omega
    rcases hi with hi | hi | hi
    · have hieq : i = (0 : Fin 3) := Fin.ext hi
      subst i
      simp [normalizedTrace, normalizedLink, backwardRC] at hdir
    · have hieq : i = (1 : Fin 3) := Fin.ext hi
      subst i
      change (u, z) ∈ rx.walk.edgeSet at he
      rw [rx_edgeSet] at he
      have : (u, z) = (r, x) := by simpa using he
      exact Vertex.noConfusion (congrArg Prod.fst this)
    · have hieq : i = (2 : Fin 3) := Fin.ext hi
      subst i
      simp [normalizedTrace, normalizedLink, backwardUX] at hdir

/-- The normalized signed route is literally the initial sublist of the
actual Lambda decoder, through the first backward departure from `x`. -/
theorem normalizedSignedSteps_sublist_decodeWalkSteps :
    List.Sublist
      [PopularAuxiliary.Input.SignedEdge.backward (r, c),
       PopularAuxiliary.Input.SignedEdge.forward (r, x),
       PopularAuxiliary.Input.SignedEdge.backward (u, x)]
      (input.decodeWalkSteps exchangePath.walk) := by
  rw [decodeWalkSteps_exchangePath]
  exact List.sublist_append_left _ _

#print axioms erasedTrace_not_contactsCoveredAtTerminal
#print axioms x_not_mem_initialSet
#print axioms no_trivial_x_component
#print axioms normalizedTrace_isTerminalRelaxedAlternating
#print axioms normalizedTrace_terminalContactSwitching
#print axioms normalizedSignedSteps_sublist_decodeWalkSteps

end GroundingLegalHiddenContactCounterexample
end Erdos599
