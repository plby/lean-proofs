/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.Defs
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Erdős Problem 63: paths, closing edges, and transport

This file records the elementary passage from a simple path to a simple
cycle.  The closing edge is required not to occur in the path; for a simple
path of length at least two this requirement follows automatically.  It also
gives convenience lemmas for transporting the exact-length predicates from
`Defs` through copies, graph embeddings, containment, and subgraphs.
-/

open Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

universe u v

variable {V : Type u} {W : Type v}
variable {G : SimpleGraph V} {H : SimpleGraph W}
variable {x y : V} {n : ℕ}

end Erdos63

namespace SimpleGraph.Walk

open Erdos63

universe u

variable {V : Type u} {G : SimpleGraph V}
variable {x y : V}

/-- Close a simple `x`--`y` path with the edge from `y` back to `x`.
The explicit edge condition rules out traversing the same edge twice. -/
theorem IsPath.isCycle_cons_of_adj_of_edge_not_mem {p : G.Walk x y}
    (hp : p.IsPath) (hyx : G.Adj y x) (hclose : s(y, x) ∉ p.edges) :
    (Walk.cons hyx p).IsCycle := by
  exact (Walk.cons_isCycle_iff p hyx).2 ⟨hp, hclose⟩

/-- An endpoint edge of a simple path can occur in the path only when the
path consists of that single edge. -/
theorem IsPath.endpoint_edge_not_mem_of_one_lt_length {p : G.Walk x y}
    (hp : p.IsPath) (hlen : 1 < p.length) : s(x, y) ∉ p.edges := by
  intro hedge
  have hpone : p.length = 1 := hp.length_eq_one_of_mem_edges hedge
  omega

/-- A simple path of length at least two closes to a simple cycle whenever
its endpoints are adjacent. -/
theorem IsPath.isCycle_cons_of_adj {p : G.Walk x y} (hp : p.IsPath)
    (hlen : 1 < p.length) (hyx : G.Adj y x) :
    (Walk.cons hyx p).IsCycle := by
  apply hp.isCycle_cons_of_adj_of_edge_not_mem hyx
  rw [Sym2.eq_swap]
  exact hp.endpoint_edge_not_mem_of_one_lt_length hlen

/-- Witness-level version of closing an exact path by an unused edge. -/
theorem IsPath.hasCycleLength_add_one_of_adj_of_edge_not_mem {p : G.Walk x y}
    (hp : p.IsPath) (hyx : G.Adj y x) (hclose : s(y, x) ∉ p.edges) :
    HasCycleLength G (p.length + 1) := by
  refine ⟨y, Walk.cons hyx p, hp.isCycle_cons_of_adj_of_edge_not_mem hyx hclose, ?_⟩
  simp [Nat.add_comm]

/-- Witness-level version in which length at least two guarantees that the
closing edge is unused. -/
theorem IsPath.hasCycleLength_add_one_of_adj {p : G.Walk x y}
    (hp : p.IsPath) (hlen : 1 < p.length) (hyx : G.Adj y x) :
    HasCycleLength G (p.length + 1) := by
  refine ⟨y, Walk.cons hyx p, hp.isCycle_cons_of_adj hlen hyx, ?_⟩
  simp [Nat.add_comm]

end SimpleGraph.Walk

namespace Erdos63

universe u v

variable {V : Type u} {W : Type v}
variable {G : SimpleGraph V} {H : SimpleGraph W}
variable {x y : V} {n : ℕ}

/-! ## Closing exact-length paths -/

/-- An exact simple path together with an unused closing edge gives an exact
simple cycle whose length is one larger. -/
theorem HasPathBetweenLength.hasCycleLength_add_one_of_adj_of_edge_not_mem
    (hpath : HasPathBetweenLength G x y n) (hyx : G.Adj y x)
    (hclose : ∀ p : G.Walk x y, p.IsPath → p.length = n → s(y, x) ∉ p.edges) :
    HasCycleLength G (n + 1) := by
  obtain ⟨p, hp, hlen⟩ := hpath
  refine ⟨y, Walk.cons hyx p, hp.isCycle_cons_of_adj_of_edge_not_mem hyx ?_, ?_⟩
  · exact hclose p hp hlen
  · simp [hlen, Nat.add_comm]

/-- A simple path of length at least two closes to a cycle when its endpoints
are adjacent. -/
theorem HasPathBetweenLength.hasCycleLength_add_one_of_adj
    (hpath : HasPathBetweenLength G x y n) (hn : 1 < n) (hyx : G.Adj y x) :
    HasCycleLength G (n + 1) := by
  obtain ⟨p, hp, hlen⟩ := hpath
  refine ⟨y, Walk.cons hyx p, hp.isCycle_cons_of_adj (hlen.symm ▸ hn) hyx, ?_⟩
  simp [hlen, Nat.add_comm]

/-- Symmetric orientation of
`HasPathBetweenLength.hasCycleLength_add_one_of_adj`. -/
theorem HasPathBetweenLength.hasCycleLength_add_one_of_adj'
    (hpath : HasPathBetweenLength G x y n) (hn : 1 < n) (hxy : G.Adj x y) :
    HasCycleLength G (n + 1) :=
  hpath.hasCycleLength_add_one_of_adj hn hxy.symm

/-! ## Transport through copies and embeddings -/

theorem HasPathBetweenLength.mapCopy (f : G.Copy H)
    (h : HasPathBetweenLength G x y n) :
    HasPathBetweenLength H (f x) (f y) n :=
  h.map f.toHom f.injective

theorem HasPathLength.mapCopy (f : G.Copy H) (h : HasPathLength G n) :
    HasPathLength H n :=
  h.map f.toHom f.injective

theorem HasCycleLength.mapCopy (f : G.Copy H) (h : HasCycleLength G n) :
    HasCycleLength H n :=
  h.map f.toHom f.injective

theorem HasPathBetweenLength.mapEmbedding (f : G ↪g H)
    (h : HasPathBetweenLength G x y n) :
    HasPathBetweenLength H (f x) (f y) n :=
  h.map f.toHom f.injective

theorem HasPathLength.mapEmbedding (f : G ↪g H) (h : HasPathLength G n) :
    HasPathLength H n :=
  h.map f.toHom f.injective

theorem HasCycleLength.mapEmbedding (f : G ↪g H) (h : HasCycleLength G n) :
    HasCycleLength H n :=
  h.map f.toHom f.injective

/-- Exact path lengths are monotone under (not necessarily induced) graph
containment. -/
theorem HasPathLength.mapIsContained (hGH : G ⊑ H) (h : HasPathLength G n) :
    HasPathLength H n :=
  h.mapCopy hGH.some

/-- Exact cycle lengths are monotone under (not necessarily induced) graph
containment. -/
theorem HasCycleLength.mapIsContained (hGH : G ⊑ H) (h : HasCycleLength G n) :
    HasCycleLength H n :=
  h.mapCopy hGH.some

/-- A path in a coerced subgraph is also a path in the ambient graph. -/
theorem HasPathLength.of_subgraph (K : G.Subgraph) (h : HasPathLength K.coe n) :
    HasPathLength G n :=
  h.mapCopy K.coeCopy

/-- A cycle in a coerced subgraph is also a cycle in the ambient graph. -/
theorem HasCycleLength.of_subgraph (K : G.Subgraph) (h : HasCycleLength K.coe n) :
    HasCycleLength G n :=
  h.mapCopy K.coeCopy

/-- A path in an induced graph is also a path in the original graph. -/
theorem HasPathLength.of_induce (S : Set V) (h : HasPathLength (G.induce S) n) :
    HasPathLength G n :=
  h.mapCopy (Copy.induce G S)

/-- A cycle in an induced graph is also a cycle in the original graph. -/
theorem HasCycleLength.of_induce (S : Set V) (h : HasCycleLength (G.induce S) n) :
    HasCycleLength G n :=
  h.mapCopy (Copy.induce G S)

/-! ## Parity in bipartite graphs -/

/-- Along a walk in a fixed bipartition, even length preserves the side and
odd length changes it.  Both conclusions are bundled so that the induction
can swap the two sides after traversing the first edge. -/
theorem _root_.SimpleGraph.IsBipartiteWith.walk_endpoint_parity
    {S T : Set V} (hb : G.IsBipartiteWith S T) (p : G.Walk x y) (hx : x ∈ S) :
    (Even p.length → y ∈ S) ∧ (Odd p.length → y ∈ T) := by
  induction p generalizing S T with
  | nil =>
      refine ⟨fun _ ↦ hx, fun hodd ↦ ?_⟩
      exact (by simpa using hodd : False).elim
  | @cons u v w hadj p ih =>
      have hv : v ∈ T := hb.mem_of_mem_adj hx hadj
      have ihp := ih hb.symm hv
      constructor
      · intro heven
        apply ihp.2
        have hcons : Even (p.length + 1) := by simpa using heven
        exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hcons)
      · intro hodd
        apply ihp.1
        have hcons : Odd (p.length + 1) := by simpa using hodd
        exact Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hcons)

theorem _root_.SimpleGraph.IsBipartiteWith.end_mem_left_of_walk_even
    {S T : Set V} (hb : G.IsBipartiteWith S T) (p : G.Walk x y)
    (hx : x ∈ S) (hp : Even p.length) : y ∈ S :=
  (hb.walk_endpoint_parity p hx).1 hp

theorem _root_.SimpleGraph.IsBipartiteWith.end_mem_right_of_walk_odd
    {S T : Set V} (hb : G.IsBipartiteWith S T) (p : G.Walk x y)
    (hx : x ∈ S) (hp : Odd p.length) : y ∈ T :=
  (hb.walk_endpoint_parity p hx).2 hp

/-- Any two walks with the same endpoints in a two-colorable graph have the
same parity. -/
theorem walk_length_mod_two_eq_of_colorable_two (hb : G.Colorable 2)
    (p q : G.Walk x y) : p.length % 2 = q.length % 2 := by
  have heven : Even (p.append q.reverse).length :=
    (SimpleGraph.two_colorable_iff_forall_loop_even.1 hb) x (p.append q.reverse)
  simp only [Walk.length_append, Walk.length_reverse] at heven
  rw [Nat.even_iff, Nat.add_mod] at heven
  omega

/-- Every cycle in a two-colorable graph has even length. -/
theorem HasCycleLength.even_of_colorable_two (hcycle : HasCycleLength G n)
    (hb : G.Colorable 2) : Even n := by
  obtain ⟨x, p, _hp, hlen⟩ := hcycle
  exact hlen ▸ (SimpleGraph.two_colorable_iff_forall_loop_even.1 hb x p)

end Erdos63
