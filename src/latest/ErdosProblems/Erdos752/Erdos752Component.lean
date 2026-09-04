/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos182.PRSEntry
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic

/-!
# Connected-component reduction for Erdős Problem 752

This file isolates two routine but type-heavy reductions used in the proof.

* Passing from a finite bipartite graph to any one of its connected components
  preserves every vertex degree, because components contain all neighbors of
  each of their vertices.
* A cycle can be mapped along any injective graph homomorphism without changing
  either simplicity or length.

The component graph embeds (in the graph-theoretic, adjacency-reflecting sense)
in the graph from which the component was taken.  If that graph is only known
to be a subgraph of a larger ambient graph, its composite map to the ambient
graph is an injective graph homomorphism; it need not reflect adjacency because
the ambient graph may contain additional edges.
-/

open SimpleGraph

namespace Erdos752

universe u v

attribute [local instance] Classical.propDecidable

section CycleMaps

variable {V : Type u} {W : Type v} {F : SimpleGraph V} {G : SimpleGraph W}

/-- Mapping a cycle along an injective graph homomorphism preserves both the
cycle property and its length. -/
lemma map_isCycle_length (f : F →g G) (hf : Function.Injective f)
    {x : V} (p : F.Walk x x) (hp : p.IsCycle) :
    (p.map f).IsCycle ∧ (p.map f).length = p.length := by
  exact ⟨hp.map hf, by simp⟩

/-- Existential form of `map_isCycle_length`, convenient for lifting a
displayed cycle length to an ambient graph. -/
lemma exists_isCycle_length_of_injectiveHom (f : F →g G)
    (hf : Function.Injective f) {l : ℕ}
    (h : ∃ x : V, ∃ p : F.Walk x x, p.IsCycle ∧ p.length = l) :
    ∃ y : W, ∃ q : G.Walk y y, q.IsCycle ∧ q.length = l := by
  obtain ⟨x, p, hp, hpl⟩ := h
  refine ⟨f x, p.map f, hp.map hf, ?_⟩
  simpa using hpl

end CycleMaps

section Components

variable {V : Type u} (H : SimpleGraph V)

/-- The canonical graph embedding of a connected component into the graph from
which it was taken. -/
abbrev componentEmbedding (c : H.ConnectedComponent) :
    c.toSimpleGraph ↪g H :=
  SimpleGraph.Embedding.induce c.supp

@[simp]
lemma componentEmbedding_apply (c : H.ConnectedComponent) (x : c) :
    componentEmbedding H c x = x.1 :=
  rfl

/-- If `H` is a subgraph of `G`, compose the component inclusion with the
identity-on-vertices homomorphism `H → G`. -/
abbrev componentHomToSupergraph {G : SimpleGraph V} (hHG : H ≤ G)
    (c : H.ConnectedComponent) : c.toSimpleGraph →g G :=
  (SimpleGraph.Hom.ofLE hHG).comp (componentEmbedding H c).toHom

@[simp]
lemma componentHomToSupergraph_apply {G : SimpleGraph V} (hHG : H ≤ G)
    (c : H.ConnectedComponent) (x : c) :
    componentHomToSupergraph H hHG c x = x.1 :=
  rfl

lemma componentHomToSupergraph_injective {G : SimpleGraph V} (hHG : H ≤ G)
    (c : H.ConnectedComponent) :
    Function.Injective (componentHomToSupergraph H hHG c) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- All neighbors of a vertex in a component lie in the same component, so
the induced component graph has exactly the original degree at that vertex. -/
lemma degree_toSimpleGraph_eq [Fintype V] [decH : DecidableRel H.Adj]
    (c : H.ConnectedComponent) (x : c) :
    c.toSimpleGraph.degree x = H.degree x.1 := by
  classical
  let : DecidableRel H.Adj := decH
  rw [← c.toSimpleGraph.card_neighborSet_eq_degree,
    Set.fintypeCard_eq_ncard,
    ← H.card_neighborSet_eq_degree,
    Set.fintypeCard_eq_ncard]
  let : DecidableRel c.toSimpleGraph.Adj := fun a b ↦ decH a.1 b.1
  have hsub : H.neighborSet x.1 ⊆ c.supp := by
    intro y hy
    exact SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp c x.2 hy
  have heq := H.degree_induce_of_neighborSet_subset (v := x) hsub
  change c.toSimpleGraph.degree x = H.degree x.1 at heq
  rw [← c.toSimpleGraph.card_neighborSet_eq_degree,
    Set.fintypeCard_eq_ncard,
    ← H.card_neighborSet_eq_degree,
    Set.fintypeCard_eq_ncard] at heq
  exact heq

/-- Bipartiteness passes to the induced graph on a connected component. -/
lemma isBipartite_toSimpleGraph (hH : H.IsBipartite)
    (c : H.ConnectedComponent) : c.toSimpleGraph.IsBipartite := by
  exact ⟨hH.some.comp (componentEmbedding H c).toHom⟩

/-- Every finite nonempty graph has a connected component.  If `H` is
bipartite and has the displayed local degree bound, that component retains
both properties.  The existential decidability witness makes the result easy
to feed into finite graph-counting lemmas. -/
theorem exists_connected_bipartite_component [Fintype V] [Nonempty V]
    [decH : DecidableRel H.Adj] {k : ℕ} (_hk : 0 < k) (hH : H.IsBipartite)
    (hdegree : ∀ x : V, k ≤ 2 * H.degree x) :
    ∃ c : H.ConnectedComponent,
      ∃ _ : DecidableRel c.toSimpleGraph.Adj,
        c.toSimpleGraph.Connected ∧
        c.toSimpleGraph.IsBipartite ∧
        ∀ x : c, k ≤ 2 * c.toSimpleGraph.degree x := by
  classical
  let : DecidableRel H.Adj := decH
  let x : V := Classical.choice (inferInstance : Nonempty V)
  let c : H.ConnectedComponent := H.connectedComponentMk x
  let : DecidableRel c.toSimpleGraph.Adj := Classical.decRel _
  refine ⟨c, inferInstance, c.connected_toSimpleGraph,
    isBipartite_toSimpleGraph H hH c, ?_⟩
  intro y
  rw [degree_toSimpleGraph_eq H c y]
  exact hdegree y.1

/-- Combined reduction from `H ≤ G`: the returned graph is finite,
connected and bipartite, has the same local lower degree bound, has a genuine
embedding into `H`, and has an injective homomorphism into `G`. -/
theorem exists_connected_bipartite_component_of_le [Fintype V] [Nonempty V]
    [decH : DecidableRel H.Adj] {G : SimpleGraph V} {k : ℕ} (hk : 0 < k)
    (hHG : H ≤ G) (hH : H.IsBipartite)
    (hdegree : ∀ x : V, k ≤ 2 * H.degree x) :
    ∃ c : H.ConnectedComponent,
      ∃ _ : DecidableRel c.toSimpleGraph.Adj,
        c.toSimpleGraph.Connected ∧
        c.toSimpleGraph.IsBipartite ∧
        (∀ x : c, k ≤ 2 * c.toSimpleGraph.degree x) ∧
        Function.Injective (componentEmbedding H c) ∧
        Function.Injective (componentHomToSupergraph H hHG c) := by
  let : DecidableRel H.Adj := decH
  obtain ⟨c, hdec, hconn, hbip, hdeg⟩ :=
    exists_connected_bipartite_component H hk hH hdegree
  refine ⟨c, hdec, hconn, hbip, hdeg,
    (componentEmbedding H c).injective,
    componentHomToSupergraph_injective H hHG c⟩

/-- A cycle in a component maps to a cycle of the same length in any ambient
supergraph of `H`. -/
lemma exists_isCycle_length_of_component_of_le {G : SimpleGraph V}
    (hHG : H ≤ G) (c : H.ConnectedComponent) {l : ℕ}
    (h : ∃ x : c, ∃ p : c.toSimpleGraph.Walk x x,
      p.IsCycle ∧ p.length = l) :
    ∃ y : V, ∃ q : G.Walk y y, q.IsCycle ∧ q.length = l := by
  exact exists_isCycle_length_of_injectiveHom
    (componentHomToSupergraph H hHG c)
    (componentHomToSupergraph_injective H hHG c) h

end Components

end Erdos752
