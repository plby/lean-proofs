/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.FullCycleCoverBank
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# The universal length-two path cover

For each unordered pair of root vertices this graph supplies `k` internally
disjoint length-two paths.  KSSS use `k = 6 m²`.  This file records the exact
finite graph and its elementary divisibility properties.
-/

namespace Erdos207

open Finset

noncomputable section

inductive PathCoverVertex (X : Type*) (k : ℕ) where
  | root (x : X)
  | middle (e : (SimpleGraph.completeGraph X).edgeSet) (i : Fin k)
  deriving DecidableEq

def pathCoverVertexEquiv (X : Type*) (k : ℕ) :
    X ⊕ ((SimpleGraph.completeGraph X).edgeSet × Fin k) ≃
      PathCoverVertex X k where
  toFun
    | Sum.inl x => .root x
    | Sum.inr (e, i) => .middle e i
  invFun
    | .root x => Sum.inl x
    | .middle e i => Sum.inr (e, i)
  left_inv x := by rcases x with (x | x) <;> try { rcases x with ⟨e, i⟩ } <;> rfl
  right_inv x := by cases x <;> rfl

noncomputable instance pathCoverVertexFintype
    {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} :
    Fintype (PathCoverVertex X k) :=
  Fintype.ofEquiv
    (X ⊕ ((SimpleGraph.completeGraph X).edgeSet × Fin k))
    (pathCoverVertexEquiv X k)

def pathCoverRel {X : Type*} [DecidableEq X] {k : ℕ} :
    PathCoverVertex X k → PathCoverVertex X k → Prop
  | .root x, .middle e _ => x ∈ e.1
  | _, _ => False

def pathCoverGraph (X : Type*) [DecidableEq X] (k : ℕ) :
    SimpleGraph (PathCoverVertex X k) :=
  SimpleGraph.fromRel pathCoverRel

instance pathCoverGraphDecidableAdj
    {X : Type*} [DecidableEq X] {k : ℕ} :
    DecidableRel (pathCoverGraph X k).Adj := by
  exact Classical.decRel _

@[simp]
lemma pathCoverGraph_adj_root_middle
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x : X) (e : (SimpleGraph.completeGraph X).edgeSet) (i : Fin k) :
    (pathCoverGraph X k).Adj (.root x) (.middle e i) ↔ x ∈ e.1 := by
  simp [pathCoverGraph, pathCoverRel]

@[simp]
lemma pathCoverGraph_adj_middle_root
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x : X) (e : (SimpleGraph.completeGraph X).edgeSet) (i : Fin k) :
    (pathCoverGraph X k).Adj (.middle e i) (.root x) ↔ x ∈ e.1 := by
  rw [SimpleGraph.adj_comm]
  exact pathCoverGraph_adj_root_middle x e i

@[simp]
lemma pathCoverGraph_not_adj_root_root
    {X : Type*} [DecidableEq X] {k : ℕ} (x y : X) :
    ¬(pathCoverGraph X k).Adj (.root x) (.root y) := by
  simp [pathCoverGraph, pathCoverRel]

@[simp]
lemma pathCoverGraph_not_adj_middle_middle
    {X : Type*} [DecidableEq X] {k : ℕ}
    (e f : (SimpleGraph.completeGraph X).edgeSet) (i j : Fin k) :
    ¬(pathCoverGraph X k).Adj (.middle e i) (.middle f j) := by
  simp [pathCoverGraph, pathCoverRel]

def pathCoverRootEmbedding {X : Type*} [DecidableEq X] {k : ℕ} :
    X ↪ PathCoverVertex X k :=
  ⟨PathCoverVertex.root, by intro x y h; simpa using h⟩

def pathCoverMiddleEmbedding {X : Type*} [DecidableEq X] {k : ℕ} :
    (SimpleGraph.completeGraph X).edgeSet × Fin k ↪ PathCoverVertex X k :=
  ⟨fun p => .middle p.1 p.2, by
    intro p q h
    cases p with
    | mk pe pi =>
      cases q with
      | mk qe qi => simpa using h⟩

def pathCoverRootNeighborEquiv
    {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} (x : X) :
    (pathCoverGraph X k).neighborSet (.root x) ≃
      (SimpleGraph.completeGraph X).incidenceSet x × Fin k where
  toFun v := by
    rcases v with ⟨v, hv⟩
    cases v with
    | root y => simpa using hv
    | middle e i =>
        exact ⟨⟨e.1, e.2, (pathCoverGraph_adj_root_middle x e i).mp hv⟩, i⟩
  invFun p :=
    ⟨.middle ⟨p.1.1, p.1.2.1⟩ p.2,
      (pathCoverGraph_adj_root_middle x ⟨p.1.1, p.1.2.1⟩ p.2).mpr
        p.1.2.2⟩
  left_inv v := by
    rcases v with ⟨v, hv⟩
    cases v with
    | root y => simpa using hv
    | middle e i => rfl
  right_inv p := by
    rcases p with ⟨⟨e, he⟩, i⟩
    rfl

lemma pathCoverGraph_degree_root
    {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} (x : X) :
    (pathCoverGraph X k).degree (.root x) =
      (Fintype.card X - 1) * k := by
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    Fintype.card_congr (pathCoverRootNeighborEquiv x), Fintype.card_prod,
    SimpleGraph.card_incidenceSet_eq_degree, SimpleGraph.complete_graph_degree,
    Fintype.card_fin]

lemma pathCoverGraph_neighborFinset_middle
    {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ}
    (e : (SimpleGraph.completeGraph X).edgeSet) (i : Fin k) :
    (pathCoverGraph X k).neighborFinset (.middle e i) =
      {PathCoverVertex.root e.1.out.1, PathCoverVertex.root e.1.out.2} := by
  ext v
  cases v with
  | root x =>
      simp only [SimpleGraph.mem_neighborFinset,
        pathCoverGraph_adj_middle_root, mem_insert, mem_singleton]
      simp only [PathCoverVertex.root.injEq]
      constructor
      · intro hx
        rw [← e.1.out_eq, Sym2.mem_iff] at hx
        exact hx
      · intro hx
        rw [← e.1.out_eq, Sym2.mem_iff]
        exact hx
  | middle f j =>
      simp

lemma pathCoverGraph_degree_middle
    {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ}
    (e : (SimpleGraph.completeGraph X).edgeSet) (i : Fin k) :
    (pathCoverGraph X k).degree (.middle e i) = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    pathCoverGraph_neighborFinset_middle]
  simp [edge_out_ne e]

def pathCoverRoots
    {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} :
    Finset (PathCoverVertex X k) :=
  univ.map pathCoverRootEmbedding

def pathCoverMiddles
    {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} :
    Finset (PathCoverVertex X k) :=
  univ.map pathCoverMiddleEmbedding

lemma pathCoverGraph_isBipartiteWith
    {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} :
    (pathCoverGraph X k).IsBipartiteWith
      ((pathCoverRoots : Finset (PathCoverVertex X k)) :
        Set (PathCoverVertex X k))
      ((pathCoverMiddles : Finset (PathCoverVertex X k)) :
        Set (PathCoverVertex X k)) := by
  constructor
  · rw [Set.disjoint_left]
    intro v hvRoot hvMiddle
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hvRoot
    obtain ⟨p, hp, h⟩ := Finset.mem_map.mp hvMiddle
    cases p with
    | mk e i =>
        simp [pathCoverMiddleEmbedding, pathCoverRootEmbedding] at h
  · intro u v huv
    cases u with
    | root x =>
        cases v with
        | root y => exact (pathCoverGraph_not_adj_root_root x y huv).elim
        | middle e i =>
            left
            constructor
            · exact Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨x, mem_univ _, rfl⟩)
            · exact Finset.mem_coe.mpr
                (Finset.mem_map.mpr ⟨(e, i), mem_univ _, rfl⟩)
    | middle e i =>
        cases v with
        | root x =>
            right
            constructor
            · exact Finset.mem_coe.mpr
                (Finset.mem_map.mpr ⟨(e, i), mem_univ _, rfl⟩)
            · exact Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨x, mem_univ _, rfl⟩)
        | middle f j =>
            exact (pathCoverGraph_not_adj_middle_middle e f i j huv).elim

lemma pathCoverGraph_card_edgeFinset
    {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} :
    (pathCoverGraph X k).edgeFinset.card =
      Fintype.card X * ((Fintype.card X - 1) * k) := by
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
    pathCoverGraph_isBipartiteWith]
  simp only [pathCoverRoots, sum_map, mem_univ, sum_const_zero, implies_true]
  change (∑ x : X, (pathCoverGraph X k).degree (.root x)) = _
  simp [pathCoverGraph_degree_root]

lemma pathCoverVertex_card
    {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ} :
    Fintype.card (PathCoverVertex X k) =
      Fintype.card X + (Fintype.card X).choose 2 * k := by
  rw [← Fintype.card_congr (pathCoverVertexEquiv X k), Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin,
    ← SimpleGraph.edgeFinset_card,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

theorem pathCoverGraph_triangleDivisible
    {X : Type*} [Fintype X] [DecidableEq X] (m : ℕ) :
    TriangleDivisible (pathCoverGraph X (6 * m ^ 2)) := by
  constructor
  · intro v
    cases v with
    | root x =>
        rw [pathCoverGraph_degree_root]
        refine ⟨3 * m ^ 2 * (Fintype.card X - 1), ?_⟩
        ring
    | middle e i =>
        rw [pathCoverGraph_degree_middle]
        exact even_two
  · rw [pathCoverGraph_card_edgeFinset]
    refine ⟨2 * m ^ 2 * (Fintype.card X * (Fintype.card X - 1)), ?_⟩
    ring

end

end Erdos207
