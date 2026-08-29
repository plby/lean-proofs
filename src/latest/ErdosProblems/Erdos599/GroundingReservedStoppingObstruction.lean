/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingMinimalSeparatingBoundary
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# Reserved-root obstruction to stopping at a minimal frontier

Avoiding one reserved grounded record repairs the backward-owner obstruction,
but does not by itself make stopping at a minimal frontier preserve roots.
Two points of an inclusion-minimal separator can occur in order on one
pre-stopped component.  Deleting every edge out of the frontier then strands
the later point behind the earlier one.

The four-vertex example below isolates exactly this issue.  The pre-stopped
relation is the path `0 -> 1 -> 3`, while the reserved source `2` is completely
disjoint from it.  The ambient web also has `2 -> 3`; hence `{1, 3}` is an
inclusion-minimal separator, with each point witnessed by a different source.
Both frontier points are rooted from the allowed source `0` before stopping,
but after deleting outgoing edges of the frontier, `3` is no longer rooted.

Thus the reserved-carrier invariant must be paired with a genuine component
transversal/antichain theorem for the chosen frontier, or with a construction
which reselects the switched relation after the frontier is fixed.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingReservedStoppingObstruction

open DirectedPath
open GroundingMinimalSeparatingBoundary

abbrev Vertex := Fin 4

/-- The ambient graph contains one path witnessing each indispensable point
of the frontier, as well as the ordered pre-stopped component. -/
def web : DWeb Vertex where
  graph := { Adj := fun x y => (x, y) ∈
    ({(0, 1), (1, 3), (2, 3)} : Set (Vertex × Vertex)) }
  source := {0, 2}
  target := {1, 3}

private theorem adj01 : web.graph.Adj 0 1 := by
  simp [web]

private theorem adj13 : web.graph.Adj 1 3 := by
  simp [web]

private theorem adj23 : web.graph.Adj 2 3 := by
  simp [web]

/-- The private ambient path which makes `1` indispensable. -/
def path01 : FinitePath web.graph where
  start := 0
  finish := 1
  walk := .cons adj01 .nil
  isPath := by
    change ([0, 1] : List Vertex).Nodup
    simp

/-- The private ambient path which makes `3` indispensable. -/
def path23 : FinitePath web.graph where
  start := 2
  finish := 3
  walk := .cons adj23 .nil
  isPath := by
    change ([2, 3] : List Vertex).Nodup
    simp

@[simp] theorem path01_support : path01.support = {0, 1} := by
  ext x
  simp [path01, FinitePath.support, Walk.support]

@[simp] theorem path23_support : path23.support = {2, 3} := by
  ext x
  simp [path23, FinitePath.support, Walk.support]

/-- Both target vertices form the stopping frontier. -/
def frontier : Set Vertex := {1, 3}

/-- The frontier separates simply because it is the whole ambient target. -/
theorem frontier_isSeparator :
    CardinalInduction.IsSeparatorFrom web web.source frontier := by
  intro a _ha p hp
  refine ⟨p.finish, p.finish_mem_support, ?_⟩
  simpa [frontier, web] using hp.2

/-- The separator is genuinely inclusion-minimal: `0 -> 1` witnesses the
necessity of `1`, and `2 -> 3` witnesses the necessity of `3`. -/
theorem frontier_isMinimalSeparator :
    CardinalInduction.IsMinimalSeparatorFrom web web.source frontier := by
  refine ⟨frontier_isSeparator, ?_⟩
  intro U hUsep hUfrontier t ht
  have ht' : t = 1 ∨ t = 3 := by
    simpa [frontier] using ht
  rcases ht' with rfl | rfl
  · have h0roof : (0 : Vertex) ∈ web.roof U := hUsep (by simp [web])
    obtain ⟨x, hxPath, hxU⟩ :=
      h0roof path01 ⟨rfl, by simp [web, path01]⟩
    have hx : x = 0 ∨ x = 1 := by
      simpa [path01_support] using hxPath
    rcases hx with rfl | rfl
    · have : (0 : Vertex) ∈ frontier := hUfrontier hxU
      simp [frontier] at this
    · exact hxU
  · have h2roof : (2 : Vertex) ∈ web.roof U := hUsep (by simp [web])
    obtain ⟨x, hxPath, hxU⟩ :=
      h2roof path23 ⟨rfl, by simp [web, path23]⟩
    have hx : x = 2 ∨ x = 3 := by
      simpa [path23_support] using hxPath
    rcases hx with rfl | rfl
    · have : (2 : Vertex) ∈ frontier := hUfrontier hxU
      simp [frontier] at this
    · exact hxU

/-- Minimality therefore supplies private ambient paths at both frontier
points, as in the grounding normalization. -/
theorem exists_privatePath_at_each_frontier_point
    {t : Vertex} (ht : t ∈ frontier) :
    ∃ a ∈ web.source, ∃ p : FinitePath web.graph,
      web.IsTargetPathFrom a p ∧ p.support ∩ frontier = {t} :=
  exists_privatePath_of_minimalSeparatingSubset frontier_isMinimalSeparator ht

/-- The component selected before frontier stopping. -/
def preStoppedEdges : Set (Vertex × Vertex) :=
  {(0, 1), (1, 3)}

/-- Literal T-aware stopping: remove every relation edge whose tail is in the
frontier. -/
def stoppedEdges : Set (Vertex × Vertex) :=
  preStoppedEdges \ {e | e.1 ∈ frontier}

theorem stoppedEdges_eq : stoppedEdges = {(0, 1)} := by
  ext e
  rcases e with ⟨x, y⟩
  simp only [stoppedEdges, preStoppedEdges, frontier, Set.mem_sdiff,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    Prod.mk.injEq]
  aesop

/-- The pre-stopped component uses only ambient edges. -/
theorem preStoppedEdges_subset_adj :
    preStoppedEdges ⊆ {e | web.graph.Adj e.1 e.2} := by
  intro e he
  rcases e with ⟨x, y⟩
  simp only [preStoppedEdges, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [web]

/-- The reserved source is wholly absent from the selected component. -/
theorem reservedSource_not_incident (x : Vertex) :
    (2, x) ∉ preStoppedEdges ∧ (x, 2) ∉ preStoppedEdges := by
  simp [preStoppedEdges]

/-- The pre-stopped relation is locally bi-unique. -/
theorem preStoppedEdges_biUnique :
    Relator.BiUnique (fun x y => (x, y) ∈ preStoppedEdges) := by
  constructor <;> intro x y z hxy hxz <;>
    simp only [preStoppedEdges, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at hxy hxz <;>
    aesop

/-- The stopped relation keeps the compiler's local bi-uniqueness. -/
theorem stoppedEdges_biUnique :
    Relator.BiUnique (fun x y => (x, y) ∈ stoppedEdges) := by
  rw [stoppedEdges_eq]
  constructor <;> intro x y z hxy hxz <;>
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hxy hxz <;>
    aesop

/-- The stopped relation keeps using only ambient edges. -/
theorem stoppedEdges_subset_adj :
    stoppedEdges ⊆ {e | web.graph.Adj e.1 e.2} := by
  intro e he
  exact preStoppedEdges_subset_adj he.1

/-- As in the Assertion 8.22 compiler, every frontier point is a sink after
the outgoing-tail cut. -/
theorem frontier_noOutgoing_stoppedEdges
    {t : Vertex} (ht : t ∈ frontier) :
    ¬ Alternating.HasOutgoing stoppedEdges t := by
  rintro ⟨y, hty⟩
  rw [stoppedEdges_eq] at hty
  have ht0 : t = 0 := by
    simpa using congrArg Prod.fst hty
  subst t
  simp [frontier] at ht

/-- Consequently the stopped frontier is even a reachability antichain.  The
failure below is therefore solely source-rootedness, not final relation
geometry. -/
theorem frontier_reachabilityAntichain_stoppedEdges :
    GroundingRootedReachabilityWarp.IsReachabilityAntichain
      stoppedEdges frontier := by
  intro b hb c _hc hbc
  rcases hbc.cases_head with hbc | ⟨d, hbd, _hdc⟩
  · exact hbc
  · exact False.elim (frontier_noOutgoing_stoppedEdges hb ⟨d, hbd⟩)

/-- Before stopping, every frontier point is rooted from a source other than
the reserved source `2`. -/
theorem every_frontier_point_preRooted :
    ∀ t ∈ frontier, ∃ a ∈ web.source \ {2},
      Relation.ReflTransGen
        (fun x y => (x, y) ∈ preStoppedEdges) a t := by
  intro t ht
  have ht' : t = 1 ∨ t = 3 := by
    simpa [frontier] using ht
  rcases ht' with rfl | rfl
  · refine ⟨0, by simp [web], Relation.ReflTransGen.single ?_⟩
    simp [preStoppedEdges]
  · refine ⟨0, by simp [web], ?_⟩
    have h01 : Relation.ReflTransGen
        (fun x y => (x, y) ∈ preStoppedEdges) (0 : Vertex) 1 :=
      Relation.ReflTransGen.single (by simp [preStoppedEdges])
    exact h01.tail (by simp [preStoppedEdges])

private def InStoppedComponent (x : Vertex) : Prop :=
  x = 0 ∨ x = 1

private theorem inStoppedComponent_of_edge
    {x y : Vertex} (hxy : (x, y) ∈ stoppedEdges)
    (hx : InStoppedComponent x) : InStoppedComponent y := by
  rw [stoppedEdges_eq] at hxy
  simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hxy
  rcases hxy with ⟨rfl, rfl⟩
  simp [InStoppedComponent]

private theorem inStoppedComponent_of_reachable
    {x y : Vertex}
    (hxy : Relation.ReflTransGen
      (fun u v => (u, v) ∈ stoppedEdges) x y)
    (hx : InStoppedComponent x) : InStoppedComponent y := by
  induction hxy with
  | refl => exact hx
  | tail _ hyz ih => exact inStoppedComponent_of_edge hyz ih

/-- T-aware stopping strands the later frontier point `3`. -/
theorem later_frontier_point_not_rooted_after_stopping :
    ¬ ∃ a ∈ web.source \ {2},
      Relation.ReflTransGen
        (fun x y => (x, y) ∈ stoppedEdges) a 3 := by
  rintro ⟨a, ha, hreach⟩
  have ha0 : a = 0 := by
    simpa [web] using ha
  subst a
  have hcomponent : InStoppedComponent 3 :=
    inStoppedComponent_of_reachable hreach (by simp [InStoppedComponent])
  simp [InStoppedComponent] at hcomponent

/-- Minimality, private paths, local bi-uniqueness, and complete avoidance of
the reserved source still do not make root reachability survive the frontier
outgoing cut. -/
theorem reserved_avoidance_and_minimality_do_not_preserve_roots :
    CardinalInduction.IsMinimalSeparatorFrom web web.source frontier ∧
      Relator.BiUnique (fun x y => (x, y) ∈ stoppedEdges) ∧
      GroundingRootedReachabilityWarp.IsReachabilityAntichain
        stoppedEdges frontier ∧
      (∀ x : Vertex,
        (2, x) ∉ preStoppedEdges ∧ (x, 2) ∉ preStoppedEdges) ∧
      (∀ t ∈ frontier, ∃ a ∈ web.source \ {2},
        Relation.ReflTransGen
          (fun x y => (x, y) ∈ preStoppedEdges) a t) ∧
      ¬ ∀ t ∈ frontier, ∃ a ∈ web.source \ {2},
        Relation.ReflTransGen
          (fun x y => (x, y) ∈ stoppedEdges) a t := by
  refine ⟨frontier_isMinimalSeparator, stoppedEdges_biUnique,
    frontier_reachabilityAntichain_stoppedEdges,
    reservedSource_not_incident, every_frontier_point_preRooted, ?_⟩
  intro hroot
  exact later_frontier_point_not_rooted_after_stopping (hroot 3 (by simp [frontier]))

end GroundingReservedStoppingObstruction
end Erdos599

#print axioms Erdos599.GroundingReservedStoppingObstruction.frontier_isMinimalSeparator
#print axioms Erdos599.GroundingReservedStoppingObstruction.reserved_avoidance_and_minimality_do_not_preserve_roots
