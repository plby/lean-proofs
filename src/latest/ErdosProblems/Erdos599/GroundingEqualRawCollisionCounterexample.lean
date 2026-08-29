/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaAlternating

/-!
# Disjoint auxiliary paths need not decode compatibly

The whole-family equal-stage switch cannot be obtained merely by taking the
union of the routes decoded from an auxiliary warp.  Distinct auxiliary
gadgets can project to the same original vertex.  In the finite example
below one auxiliary path uses the old gadget `.old b`, while another uses
the distinct edge gadget `.edge a b`.  The two auxiliary paths are
vertex-disjoint, but their decoded forward connectors both enter `b`.

After symmetric difference with the one ladder path, the two incoming edges
survive.  Thus the raw simultaneous switched relation is not bi-unique.  A
sound strong-target construction needs a simultaneous avoidance/closure
theorem; auxiliary-warp disjointness alone is insufficient.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingEqualRawCollisionCounterexample

open DirectedPath Alternating

inductive Vertex
  | a | b | x | w | y
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj u v :=
    (u = a ∧ v = b) ∨ (u = b ∧ v = y) ∨
    (u = x ∧ v = b) ∨ (u = w ∧ v = b) ∨
    (u = a ∧ v = y)

@[simp] theorem graph_adj (u v : Vertex) :
    graph.Adj u v ↔
      (u = a ∧ v = b) ∨ (u = b ∧ v = y) ∨
      (u = x ∧ v = b) ∨ (u = w ∧ v = b) ∨
      (u = a ∧ v = y) :=
  Iff.rfl

def aby : FinitePath graph where
  start := a
  finish := y
  walk := Walk.cons (u := a) (v := b) (w := y) (by simp [graph])
    (Walk.cons (u := b) (v := y) (w := y) (by simp [graph]) Walk.nil)
  isPath := by
    change [a, b, y].Nodup
    simp

@[simp] theorem aby_start : aby.start = a := rfl
@[simp] theorem aby_finish : aby.finish = y := rfl

@[simp] theorem aby_support : aby.support = ({a, b, y} : Set Vertex) := by
  ext z
  change z ∈ [a, b, y] ↔ _
  simp

@[simp] theorem aby_edgeSet :
    aby.walk.edgeSet = ({(a, b), (b, y)} : Set (Vertex × Vertex)) := by
  ext e
  simp [aby, DirectedPath.Walk.edgeSet, or_comm]

def web : DWeb Vertex where
  graph := graph
  source := {x, w}
  target := {y}

def ladderPaths : Set web.DPath := {Sum.inl aby}

theorem ladderPaths_isWarp : web.IsWarp ladderPaths := by
  intro p hp q hq hpq
  simp only [ladderPaths] at hp hq
  exact False.elim (hpq (hp.trans hq.symm))

def ladder : web.Warp := ⟨ladderPaths, ladderPaths_isWarp⟩

def input : PopularAuxiliary.Input web Empty where
  ladder := ladder
  groundedRecords := ∅
  finiteSource := {x, w}
  markerSet := {b, y}
  proxyPath i := nomatch i
  proxy_isRay i := nomatch i

abbrev LV := PopularAuxiliary.Input.LambdaVertex Vertex Empty

@[simp] theorem input_ladder_paths : input.ladder.paths = ladderPaths := rfl
@[simp] theorem input_finiteSource : input.finiteSource = {x, w} := rfl
@[simp] theorem input_markerSet : input.markerSet = {b, y} := rfl

@[simp] theorem terminalFrontier_ladderPaths :
    web.terminalFrontier ladderPaths = ({y} : Set Vertex) := by
  ext z
  constructor
  · rintro ⟨p, hp, hpz⟩
    have hpaby : p = (Sum.inl aby : web.DPath) :=
      Set.mem_singleton_iff.mp hp
    subst p
    exact Option.some.inj hpz.symm
  · intro hz
    have hzy : z = y := by simpa using hz
    subst z
    exact ⟨Sum.inl aby, Set.mem_singleton _, rfl⟩

@[simp] theorem web_essential_singleton_y :
    web.essential ({y} : Set Vertex) = {y} := by
  apply Set.Subset.antisymm (web.essential_subset {y})
  intro z hz
  have hzy : z = y := by simpa using hz
  subst z
  refine ⟨by simp, ?_⟩
  rw [web.not_mem_roof_iff]
  refine ⟨FinitePath.trivial graph y, ⟨rfl, by simp [web]⟩, ?_⟩
  simp [DWeb.Avoids]

@[simp] theorem input_essentialLadder :
    input.essentialLadder = ladderPaths := by
  ext p
  constructor
  · exact fun hp ↦ hp.1
  · intro hp
    have hpaby : p = (Sum.inl aby : web.DPath) :=
      Set.mem_singleton_iff.mp hp
    subst p
    refine ⟨Set.mem_singleton _, y, rfl, ?_⟩
    simp

@[simp] theorem input_targetMarkers :
    input.targetMarkers = ({b, y} : Set Vertex) := by
  ext z
  constructor
  · intro hz
    exact hz.1
  · intro hz
    refine ⟨hz, ?_⟩
    rw [input_essentialLadder]
    refine ⟨Sum.inl aby, Set.mem_singleton _, ?_⟩
    change z ∈ aby.support
    rw [aby_support]
    rcases hz with rfl | rfl <;> simp

theorem ab_mem_familyEdges : (a, b) ∈ input.familyEdges := by
  refine ⟨Sum.inl aby, Set.mem_singleton _, ?_⟩
  change (a, b) ∈ aby.walk.edgeSet
  rw [aby_edgeSet]
  simp

def xb : FinitePath input.lambda.graph where
  start := .old x
  finish := .old b
  walk := .cons (by
    rw [input.lambda_adj_old_old]
    exact ⟨Or.inr (by simp), Or.inr (by simp), by simp [web, graph]⟩) .nil
  isPath := by
    change [(.old x : LV), .old b].Nodup
    simp

def waby : FinitePath input.lambda.graph where
  start := .old w
  finish := .old y
  walk := .cons (by
      rw [input.lambda_adj_old_edge]
      refine ⟨ab_mem_familyEdges, Or.inr ⟨Or.inr (by simp), ?_⟩⟩
      simp [web, graph])
    (.cons (by
      rw [input.lambda_adj_edge_old]
      exact ⟨ab_mem_familyEdges, Or.inr
        ⟨Or.inr (by simp), by simp [web, graph]⟩⟩) .nil)
  isPath := by
    change [(.old w : LV), .edge a b, .old y].Nodup
    simp

@[simp] theorem xb_start : xb.start = .old x := rfl
@[simp] theorem xb_finish : xb.finish = .old b := rfl
@[simp] theorem waby_start : waby.start = .old w := rfl
@[simp] theorem waby_finish : waby.finish = .old y := rfl

@[simp] theorem xb_support :
    xb.support = ({(.old x : LV), .old b} : Set LV) := by
  ext z
  change z ∈ [(.old x : LV), .old b] ↔ _
  simp

@[simp] theorem waby_support :
    waby.support = ({(.old w : LV), .edge a b, .old y} : Set LV) := by
  ext z
  change z ∈ [(.old w : LV), .edge a b, .old y] ↔ _
  simp

def auxiliaryPaths : Set (FinitePath input.lambda.graph) := {xb, waby}

theorem auxiliaryPaths_pairwiseDisjoint :
    auxiliaryPaths.PairwiseDisjoint FinitePath.support := by
  intro p hp q hq hpq
  simp only [auxiliaryPaths, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact False.elim (hpq rfl)
  · change Disjoint xb.support waby.support
    rw [xb_support, waby_support]
    simp [Set.disjoint_left]
  · change Disjoint waby.support xb.support
    rw [xb_support, waby_support]
    exact (by simp [Set.disjoint_left] :
      Disjoint ({(.old x : LV), .old b} : Set LV)
        ({(.old w : LV), .edge a b, .old y} : Set LV)).symm
  · exact False.elim (hpq rfl)

def auxiliaryWarp : Popular.XSWarp input.lambda input.lambda.target where
  paths := auxiliaryPaths
  disjoint := auxiliaryPaths_pairwiseDisjoint
  starts_in_source := by
    intro p hp
    simp only [auxiliaryPaths, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact (input.mem_lambda_source_old x).2 (by simp)
    · exact (input.mem_lambda_source_old w).2 (by simp)
  ends_in_target := by
    intro p hp
    simp only [auxiliaryPaths, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact (input.mem_lambda_target_old b).2 (by simp)
    · exact (input.mem_lambda_target_old y).2 (by simp)

private theorem chosenConnector_xb :
    input.chosenConnector? (.old x) (.old b) = some (x, b) := by
  have hadj : input.lambda.graph.Adj (.old x) (.old b) := by
    rw [input.lambda_adj_old_old]
    exact ⟨Or.inr (by simp), Or.inr (by simp), by simp [web, graph]⟩
  cases hopt : input.chosenConnector? (.old x) (.old b) with
  | none =>
      have hjoin := input.chosenConnector?_eq_none_of_adj hadj hopt
      simp [PopularAuxiliary.Input.BackwardJoin] at hjoin
  | some e =>
      have hconnector := input.chosenConnector?_eq_some hopt
      have hfst : e.1 = x := by
        rcases hconnector.1 with hexit | hproxy
        · exact (Option.some.inj hexit).symm
        · obtain ⟨i, hi, _⟩ := hproxy
          cases hi
      have hsnd : e.2 = b :=
        (Option.some.inj hconnector.2.1).symm
      have he : e = (x, b) := Prod.ext hfst hsnd
      exact congrArg some he

private theorem chosenConnector_wb :
    input.chosenConnector? (.old w) (.edge a b) = some (w, b) := by
  have hadj : input.lambda.graph.Adj (.old w) (.edge a b) := by
    rw [input.lambda_adj_old_edge]
    refine ⟨ab_mem_familyEdges, Or.inr ⟨Or.inr (by simp), ?_⟩⟩
    simp [web, graph]
  cases hopt : input.chosenConnector? (.old w) (.edge a b) with
  | none =>
      have hjoin := input.chosenConnector?_eq_none_of_adj hadj hopt
      simp [PopularAuxiliary.Input.BackwardJoin] at hjoin
  | some e =>
      have hconnector := input.chosenConnector?_eq_some hopt
      have hfst : e.1 = w := by
        rcases hconnector.1 with hexit | hproxy
        · exact (Option.some.inj hexit).symm
        · obtain ⟨i, hi, _⟩ := hproxy
          cases hi
      have hsnd : e.2 = b :=
        (Option.some.inj hconnector.2.1).symm
      have he : e = (w, b) := Prod.ext hfst hsnd
      exact congrArg some he

theorem xb_connector_mem_decodedRouteEdges :
    (x, b) ∈ input.decodedRouteEdges xb := by
  apply Or.inr
  exact ⟨.old x, .old b, by simp [xb, FinitePath.edgeSet],
    chosenConnector_xb⟩

theorem wb_connector_mem_decodedRouteEdges :
    (w, b) ∈ input.decodedRouteEdges waby := by
  apply Or.inr
  exact ⟨.old w, .edge a b, by
    simp [waby, FinitePath.edgeSet], chosenConnector_wb⟩

/-- Literal union of the two raw decoded route relations. -/
def decodedFamilyRouteEdges : Set (Vertex × Vertex) :=
  ⋃ p ∈ auxiliaryWarp.paths, input.decodedRouteEdges p

theorem xb_connector_mem_decodedFamilyRouteEdges :
    (x, b) ∈ decodedFamilyRouteEdges := by
  exact Set.mem_iUnion.2 ⟨xb, Set.mem_iUnion.2
    ⟨Or.inl rfl, xb_connector_mem_decodedRouteEdges⟩⟩

theorem wb_connector_mem_decodedFamilyRouteEdges :
    (w, b) ∈ decodedFamilyRouteEdges := by
  exact Set.mem_iUnion.2 ⟨waby, Set.mem_iUnion.2
    ⟨Or.inr rfl, wb_connector_mem_decodedRouteEdges⟩⟩

theorem xb_not_mem_familyEdges : (x, b) ∉ input.familyEdges := by
  rintro ⟨p, hp, he⟩
  have hpaby : p = (Sum.inl aby : web.DPath) :=
    Set.mem_singleton_iff.mp hp
  subst p
  change (x, b) ∈ aby.walk.edgeSet at he
  rw [aby_edgeSet] at he
  simp at he

theorem wb_not_mem_familyEdges : (w, b) ∉ input.familyEdges := by
  rintro ⟨p, hp, he⟩
  have hpaby : p = (Sum.inl aby : web.DPath) :=
    Set.mem_singleton_iff.mp hp
  subst p
  change (w, b) ∈ aby.walk.edgeSet at he
  rw [aby_edgeSet] at he
  simp at he

/-- The raw whole-family switch relation. -/
def switchedEdges : Set (Vertex × Vertex) :=
  edgeSymmDiff input.familyEdges decodedFamilyRouteEdges

theorem xb_mem_switchedEdges : (x, b) ∈ switchedEdges :=
  Or.inr ⟨xb_connector_mem_decodedFamilyRouteEdges,
    xb_not_mem_familyEdges⟩

theorem wb_mem_switchedEdges : (w, b) ∈ switchedEdges :=
  Or.inr ⟨wb_connector_mem_decodedFamilyRouteEdges,
    wb_not_mem_familyEdges⟩

/-- Although `auxiliaryWarp` is a genuine vertex-disjoint target warp, its
raw decoded simultaneous switch has two distinct predecessors of `b`. -/
theorem raw_simultaneous_switch_not_biUnique :
    ¬ Relator.BiUnique (fun u v ↦ (u, v) ∈ switchedEdges) := by
  intro h
  have hxw : x = w := h.1 xb_mem_switchedEdges wb_mem_switchedEdges
  cases hxw

#print axioms raw_simultaneous_switch_not_biUnique

end GroundingEqualRawCollisionCounterexample
end Erdos599
