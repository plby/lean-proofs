/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingPrefix
import ErdosProblems.Erdos599.SafeSwitching
import Mathlib.Tactic.FinCases

/-!
# Filling a reference-owner gap may require another augmenting component

For two endpoint-aligned finite warps, the reference edges used by one
augmenting matching component need not form an interval on each reference
owner.  Closing such a gap need not merely add a matching cycle: it can force
an edge belonging to a second augmenting component, with its own two exposed
endpoints.

The finite example is

* `W = {u-c-q, r-a, b-d-v, z-t}`;
* `Y = {b-a, z-c-d-t}`.

The component from `u` to `v` uses the first and last edges of `z-c-d-t`.
Any interval-convex removal containing these two edges must also contain
`c-d`.  But `c-d` lies in the distinct augmenting matching component from
`r` to `q`.  All four displayed families have their initials in the common
source set and terminals in the common target set of a normalized web.
Thus a pairwise gap-filling construction cannot assume that all added
components are cycles, even under the endpoint purity used in the actual
application.
-/

namespace Erdos599
namespace TwoWarpMatchingGapRepairObstruction

open Set
open _root_.Erdos599.DirectedPath
open Alternating
open TwoWarpMatchingTraversal

inductive Vertex
  | u | c | q | r | a | b | d | v | z | t
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj x y :=
    (x = u ∧ y = c) ∨ (x = c ∧ y = q) ∨ (x = r ∧ y = a) ∨
    (x = b ∧ y = d) ∨ (x = d ∧ y = v) ∨
    (x = z ∧ y = t) ∨ (x = b ∧ y = a) ∨
    (x = z ∧ y = c) ∨ (x = c ∧ y = d) ∨ (x = d ∧ y = t)

private def edgePath (x y : Vertex) (hxy : graph.Adj x y) : FinitePath graph where
  start := x
  finish := y
  walk := .cons hxy .nil
  isPath := by
    change [x, y].Nodup
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

def ra : FinitePath graph := edgePath r a (by simp [graph])
def zt : FinitePath graph := edgePath z t (by simp [graph])
def ba : FinitePath graph := edgePath b a (by simp [graph])

def ucq : FinitePath graph where
  start := u
  finish := q
  walk := Walk.cons (u := u) (v := c) (w := q) (by simp [graph])
    (Walk.cons (u := c) (v := q) (w := q) (by simp [graph]) Walk.nil)
  isPath := by
    change [u, c, q].Nodup
    simp

def bdv : FinitePath graph where
  start := b
  finish := v
  walk := Walk.cons (u := b) (v := d) (w := v) (by simp [graph])
    (Walk.cons (u := d) (v := v) (w := v) (by simp [graph]) Walk.nil)
  isPath := by
    change [b, d, v].Nodup
    simp

def zcdt : FinitePath graph where
  start := z
  finish := t
  walk := Walk.cons (u := z) (v := c) (w := t) (by simp [graph])
    (Walk.cons (u := c) (v := d) (w := t) (by simp [graph])
      (Walk.cons (u := d) (v := t) (w := t) (by simp [graph]) Walk.nil))
  isPath := by
    change [z, c, d, t].Nodup
    simp

@[simp] private theorem edgePath_support (x y : Vertex) (hxy : graph.Adj x y) :
    (edgePath x y hxy).support = {x, y} := by
  ext q
  simp [edgePath, FinitePath.support, Walk.support]

@[simp] private theorem edgePath_edgeSet (x y : Vertex) (hxy : graph.Adj x y) :
    (edgePath x y hxy).edgeSet = {(x, y)} := by
  ext e
  simp [edgePath, FinitePath.edgeSet, Walk.edgeSet]

@[simp] theorem ra_support : ra.support = {r, a} := edgePath_support _ _ _
@[simp] theorem zt_support : zt.support = {z, t} := edgePath_support _ _ _
@[simp] theorem ba_support : ba.support = {b, a} := edgePath_support _ _ _

@[simp] theorem ra_edgeSet : ra.edgeSet = {(r, a)} := edgePath_edgeSet _ _ _
@[simp] theorem zt_edgeSet : zt.edgeSet = {(z, t)} := edgePath_edgeSet _ _ _
@[simp] theorem ba_edgeSet : ba.edgeSet = {(b, a)} := edgePath_edgeSet _ _ _

@[simp] theorem ucq_support : ucq.support = {u, c, q} := by
  ext x
  simp [FinitePath.support, ucq, Walk.support]

@[simp] theorem ucq_edgeSet : ucq.edgeSet = {(u, c), (c, q)} := by
  ext e
  simp [ucq, FinitePath.edgeSet, Walk.edgeSet]
  aesop

@[simp] theorem bdv_support : bdv.support = {b, d, v} := by
  ext x
  simp [FinitePath.support, bdv, Walk.support]

@[simp] theorem bdv_edgeSet : bdv.edgeSet = {(b, d), (d, v)} := by
  ext e
  simp [bdv, FinitePath.edgeSet, Walk.edgeSet]
  aesop

@[simp] theorem zcdt_support : zcdt.support = {z, c, d, t} := by
  ext x
  simp [FinitePath.support, zcdt, Walk.support]

@[simp] theorem zcdt_edgeSet :
    zcdt.edgeSet = {(z, c), (c, d), (d, t)} := by
  ext e
  simp [zcdt, FinitePath.edgeSet, Walk.edgeSet]
  aesop

abbrev web : DWeb Vertex where
  graph := graph
  source := {u, r, b, z}
  target := {q, a, v, t}

def W : Set web.DPath :=
  {Sum.inl ucq, Sum.inl ra, Sum.inl bdv, Sum.inl zt}

def Y : Set web.DPath := {Sum.inl ba, Sum.inl zcdt}

theorem W_isWarp : web.IsWarp W := by
  intro p hp q hq hpq
  simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl
  · exact (hpq rfl).elim
  · change Disjoint ucq.support ra.support
    rw [ucq_support, ra_support]
    simp [Set.disjoint_left]
  · change Disjoint ucq.support bdv.support
    rw [ucq_support, bdv_support]
    simp [Set.disjoint_left]
  · change Disjoint ucq.support zt.support
    rw [ucq_support, zt_support]
    simp [Set.disjoint_left]
  · change Disjoint ra.support ucq.support
    rw [ra_support, ucq_support]
    simp [Set.disjoint_left]
  · exact (hpq rfl).elim
  · change Disjoint ra.support bdv.support
    rw [ra_support, bdv_support]
    simp [Set.disjoint_left]
  · change Disjoint ra.support zt.support
    rw [ra_support, zt_support]
    simp [Set.disjoint_left]
  · change Disjoint bdv.support ucq.support
    rw [bdv_support, ucq_support]
    simp [Set.disjoint_left]
  · change Disjoint bdv.support ra.support
    rw [bdv_support, ra_support]
    simp [Set.disjoint_left]
  · exact (hpq rfl).elim
  · change Disjoint bdv.support zt.support
    rw [bdv_support, zt_support]
    simp [Set.disjoint_left]
  · change Disjoint zt.support ucq.support
    rw [zt_support, ucq_support]
    simp [Set.disjoint_left]
  · change Disjoint zt.support ra.support
    rw [zt_support, ra_support]
    simp [Set.disjoint_left]
  · change Disjoint zt.support bdv.support
    rw [zt_support, bdv_support]
    simp [Set.disjoint_left]
  · exact (hpq rfl).elim

theorem Y_isWarp : web.IsWarp Y := by
  intro p hp q hq hpq
  simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (hpq rfl).elim
  · change Disjoint ba.support zcdt.support
    rw [ba_support, zcdt_support]
    simp [Set.disjoint_left]
  · change Disjoint zcdt.support ba.support
    rw [zcdt_support, ba_support]
    simp [Set.disjoint_left]
  · exact (hpq rfl).elim

theorem Y_initialSet_subset_W : web.initialSet Y ⊆ web.initialSet W := by
  rintro x ⟨p, hp, rfl⟩
  simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨.inl bdv, by simp [W], rfl⟩
  · exact ⟨.inl zt, by simp [W], rfl⟩

theorem Y_terminalFrontier_subset_W :
    web.terminalFrontier Y ⊆ web.terminalFrontier W := by
  rintro x ⟨p, hp, hpx⟩
  simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · have hx : x = a := by simpa [ba, edgePath] using Option.some.inj hpx.symm
    subst x
    exact ⟨.inl ra, by simp [W], rfl⟩
  · have hx : x = t := by simpa [zcdt] using Option.some.inj hpx.symm
    subst x
    exact ⟨.inl zt, by simp [W], rfl⟩

theorem web_isNormalized : web.IsNormalized := by
  intro x y hxy
  constructor
  · intro hy
    simp only [web, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> simp [graph] at hxy
  · intro hx
    simp only [web, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [graph] at hxy

theorem W_initialSet_subset_source : web.initialSet W ⊆ web.source := by
  rintro x ⟨p, hp, rfl⟩
  simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · change ucq.start ∈ web.source
    simp [ucq, web]
  · change ra.start ∈ web.source
    simp [ra, edgePath, web]
  · change bdv.start ∈ web.source
    simp [bdv, web]
  · change zt.start ∈ web.source
    simp [zt, edgePath, web]

theorem W_terminalFrontier_subset_target :
    web.terminalFrontier W ⊆ web.target := by
  rintro x ⟨p, hp, hpx⟩
  simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · have hx : x = q := by simpa [ucq] using Option.some.inj hpx.symm
    subst x
    simp [web]
  · have hx : x = a := by simpa [ra, edgePath] using Option.some.inj hpx.symm
    subst x
    simp [web]
  · have hx : x = v := by simpa [bdv] using Option.some.inj hpx.symm
    subst x
    simp [web]
  · have hx : x = t := by simpa [zt, edgePath] using Option.some.inj hpx.symm
    subst x
    simp [web]

def mainRemoved : Set (Vertex × Vertex) := {(z, c), (d, t)}

/-- The first augmenting component deletes two separated edges of one
reference owner. -/
theorem mainRemoved_mem_ends :
    (z, c) ∈ mainRemoved ∧ (d, t) ∈ mainRemoved := by simp [mainRemoved]

theorem mainRemoved_misses_gap : (c, d) ∉ mainRemoved := by
  simp [mainRemoved]

/-- Interval convexity forces the middle edge of `z-c-d-t` as soon as the
two end edges are removed. -/
theorem interval_closure_forces_gap
    {R : Set (Vertex × Vertex)}
    (hinterval : IsEdgeInterval (R ∩ zcdt.edgeSet)
      (.inl zcdt : web.DPath))
    (hzc : (z, c) ∈ R) (hdt : (d, t) ∈ R) :
    (c, d) ∈ R := by
  have hzcE : (z, c) ∈ R ∩ zcdt.edgeSet := by
    refine ⟨hzc, ?_⟩
    simp [zcdt, FinitePath.edgeSet, Walk.edgeSet]
  have hdtE : (d, t) ∈ R ∩ zcdt.edgeSet := by
    refine ⟨hdt, ?_⟩
    simp [zcdt, FinitePath.edgeSet, Walk.edgeSet]
  have hcd : (c, d) ∈ zcdt.edgeSet := by
    simp [zcdt, FinitePath.edgeSet, Walk.edgeSet]
  have hmem := IsEdgeInterval.mem_of_between_positions hinterval
    hzcE hdtE hcd (e := (c, d)) (by decide) (by decide)
  exact hmem.1

private theorem exclusive_WY_uc : Exclusive W Y u c := by
  constructor
  · exact matchingEdge_actual (by
      simp [W, familyEdges, ucq, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [Y, familyEdges, ba, zcdt, edgePath,
        FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_YW_zc : Exclusive Y W z c := by
  constructor
  · exact matchingEdge_actual (by
      simp [Y, familyEdges, zcdt, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [W, familyEdges, ucq, ra, bdv, zt, edgePath,
        FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_WY_zt : Exclusive W Y z t := by
  constructor
  · exact matchingEdge_actual (by
      simp [W, familyEdges, zt, edgePath, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [Y, familyEdges, ba, zcdt, edgePath,
        FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_YW_dt : Exclusive Y W d t := by
  constructor
  · exact matchingEdge_actual (by
      simp [Y, familyEdges, zcdt, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [W, familyEdges, ucq, ra, bdv, zt, edgePath,
        FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_WY_dv : Exclusive W Y d v := by
  constructor
  · exact matchingEdge_actual (by
      simp [W, familyEdges, bdv, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [Y, familyEdges, ba, zcdt, edgePath,
        FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_WY_ra : Exclusive W Y r a := by
  constructor
  · exact matchingEdge_actual (by
      simp [W, familyEdges, ra, edgePath, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [Y, familyEdges, ba, zcdt, edgePath,
        FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_YW_ba : Exclusive Y W b a := by
  constructor
  · exact matchingEdge_actual (by
      simp [Y, familyEdges, ba, edgePath, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [W, familyEdges, ucq, ra, bdv, zt, edgePath,
        FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_WY_bd : Exclusive W Y b d := by
  constructor
  · exact matchingEdge_actual (by
      simp [W, familyEdges, bdv, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [Y, familyEdges, ba, zcdt, edgePath,
        FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_YW_cd : Exclusive Y W c d := by
  constructor
  · exact matchingEdge_actual (by
      simp [Y, familyEdges, zcdt, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [W, familyEdges, ucq, ra, bdv, zt, edgePath,
        FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

private theorem exclusive_WY_cq : Exclusive W Y c q := by
  constructor
  · exact matchingEdge_actual (by
      simp [W, familyEdges, ucq, FinitePath.edgeSet, Walk.edgeSet])
  · intro h
    rcases h with h | h
    · simp [Y, familyEdges, ba, zcdt, edgePath,
        FinitePath.edgeSet, Walk.edgeSet] at h
    · exact Vertex.noConfusion h.1

def mainPort (i : Fin 6) : Port Vertex :=
  match i.1 with
  | 0 => .inl u
  | 1 => .inr c
  | 2 => .inl z
  | 3 => .inr t
  | 4 => .inl d
  | _ => .inr v

def companionPort (i : Fin 6) : Port Vertex :=
  match i.1 with
  | 0 => .inl r
  | 1 => .inr a
  | 2 => .inl b
  | 3 => .inr d
  | 4 => .inl c
  | _ => .inr q

/-- The root component from `u` to `v`. -/
def mainPrefix : FinitePortPrefix W Y u where
  lastIndex := 5
  positive := by omega
  port := mainPort
  starts := rfl
  steps := by
    intro i
    fin_cases i
    · exact exclusive_WY_uc
    · exact exclusive_YW_zc
    · exact exclusive_WY_zt
    · exact exclusive_YW_dt
    · exact exclusive_WY_dv
  injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [mainPort] at hij ⊢

/-- The gap edge belongs to a second augmenting component, from `r` to `q`,
not to a cycle. -/
def companionPrefix : FinitePortPrefix W Y r where
  lastIndex := 5
  positive := by omega
  port := companionPort
  starts := rfl
  steps := by
    intro i
    fin_cases i
    · exact exclusive_WY_ra
    · exact exclusive_YW_ba
    · exact exclusive_WY_bd
    · exact exclusive_YW_cd
    · exact exclusive_WY_cq
  injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [companionPort] at hij ⊢

theorem mainPrefix_terminal :
    mainPrefix.projectedVertex ⟨5, by change 5 < 6; omega⟩ = v := rfl

theorem companionPrefix_terminal :
    companionPrefix.projectedVertex ⟨5, by change 5 < 6; omega⟩ = q := rfl

theorem companion_endpoints_distinct : r ≠ q := by decide

/-- Endpoint alignment does not make gap-filling components cyclic: the
middle edge forced by interval convexity lies on the displayed second
augmenting path with distinct projected endpoints. -/
theorem forced_gap_lies_on_distinct_augmenting_component :
    web.initialSet Y ⊆ web.initialSet W ∧
      web.terminalFrontier Y ⊆ web.terminalFrontier W ∧
      mainPrefix.projectedVertex 0 = u ∧
      mainPrefix.projectedVertex ⟨5, by change 5 < 6; omega⟩ = v ∧
      companionPrefix.projectedVertex 0 = r ∧
      companionPrefix.projectedVertex ⟨5, by change 5 < 6; omega⟩ = q ∧ r ≠ q := by
  exact ⟨Y_initialSet_subset_W, Y_terminalFrontier_subset_W,
    rfl, rfl, rfl, rfl, by decide⟩

#print axioms W_isWarp
#print axioms Y_isWarp
#print axioms web_isNormalized
#print axioms W_initialSet_subset_source
#print axioms W_terminalFrontier_subset_target
#print axioms interval_closure_forces_gap
#print axioms forced_gap_lies_on_distinct_augmenting_component

end TwoWarpMatchingGapRepairObstruction
end Erdos599
