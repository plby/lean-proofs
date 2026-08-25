/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.PippengerSpencerEdgeColoring
import ErdosProblems.Erdos622.LinearForest

/-!
# Rank-two input for the Pippenger--Spencer schedule

This module records the exact translation from a finite simple graph to the
rank-two indexed hypergraph used by the Pippenger--Spencer development.  In
particular, graph degree becomes hypergraph edge-degree, distinct-vertex
codegree is at most one, and a hypergraph matching gives a graph-level
matching.  These facts isolate the analytic schedule and inner marginal
statements from the graph bookkeeping needed for Erdős 622.
-/

open Finset

namespace Erdos622

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PippengerSchedule

open Erdos76

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The edge-indexed rank-two hypergraph associated with a finite simple
graph. -/
def graphHypergraph (G : SimpleGraph V) :
    FiniteHypergraph V G.edgeSet where
  vertexSet := Finset.univ
  support e := e.1.toFinset
  support_subset_vertexSet _ := Finset.subset_univ _

@[simp] lemma graphHypergraph_vertexSet (G : SimpleGraph V) :
    (graphHypergraph G).vertexSet = Finset.univ := rfl

@[simp] lemma graphHypergraph_support (G : SimpleGraph V) (e : G.edgeSet) :
    (graphHypergraph G).support e = e.1.toFinset := rfl

/-- Graph edges have exactly two endpoints, so the associated hypergraph is
two-uniform. -/
lemma graphHypergraph_isUniform_two (G : SimpleGraph V) :
    (graphHypergraph G).IsUniform 2 := by
  intro e
  exact Sym2.card_toFinset_of_not_isDiag e.1
    (G.not_isDiag_of_mem_edgeSet e.2)

/-- Hypergraph incidence degree agrees with ordinary graph degree. -/
lemma graphHypergraph_edgeDegree (G : SimpleGraph V) (v : V) :
    (graphHypergraph G).edgeDegree v = G.degree v := by
  rw [Erdos76.FiniteHypergraph.edgeDegree]
  change ((Finset.univ : Finset G.edgeSet).filter
      fun e => v ∈ e.1.toFinset).card = G.degree v
  rw [← G.card_incidenceFinset_eq_degree,
    G.incidenceFinset_eq_filter]
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_edgeFinset.mpr e.2, Sym2.mem_toFinset.mp he⟩
  · intro e₁ h₁ e₂ h₂ heq
    exact Subtype.ext heq
  · intro e he
    refine ⟨⟨e, SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp he).1⟩,
      ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Sym2.mem_toFinset.mpr (Finset.mem_filter.mp he).2

/-- Two distinct vertices of a simple graph lie together in at most one
edge. -/
lemma graphHypergraph_edgePairDegree_le_one (G : SimpleGraph V)
    {u v : V} (huv : u ≠ v) :
    (graphHypergraph G).edgePairDegree u v ≤ 1 := by
  rw [Erdos76.FiniteHypergraph.edgePairDegree]
  apply Finset.card_le_one.mpr
  intro e he f hf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he hf
  apply Subtype.ext
  have heq : e.1 = s(u, v) :=
    (Sym2.mem_and_mem_iff huv).mp
      ⟨Sym2.mem_toFinset.mp he.1, Sym2.mem_toFinset.mp he.2⟩
  have hfeq : f.1 = s(u, v) :=
    (Sym2.mem_and_mem_iff huv).mp
      ⟨Sym2.mem_toFinset.mp hf.1, Sym2.mem_toFinset.mp hf.2⟩
  exact heq.trans hfeq.symm

/-- A matching of edge indices determines the corresponding spanning
matching subgraph. -/
def matchingSubgraph (G : SimpleGraph V) (M : Finset G.edgeSet) :
    SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ he : e ∈ G.edgeSet, (⟨e, he⟩ : G.edgeSet) ∈ M}

lemma matchingSubgraph_le (G : SimpleGraph V) (M : Finset G.edgeSet) :
    matchingSubgraph G M ≤ G := by
  rw [matchingSubgraph, SimpleGraph.fromEdgeSet_le]
  intro e he
  exact he.1.choose

/-- The matching subgraph retains exactly the selected edge indices. -/
lemma map_matchingSubgraph_eq_edgeFinset (G : SimpleGraph V)
    (M : Finset G.edgeSet) :
    M.map (Function.Embedding.subtype G.edgeSet) =
      (matchingSubgraph G M).edgeFinset := by
  ext e
  simp only [Finset.mem_map, SimpleGraph.mem_edgeFinset]
  constructor
  · rintro ⟨a, ha, rfl⟩
    change a.1 ∈ (matchingSubgraph G M).edgeSet
    rw [matchingSubgraph, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨⟨a.2, ha⟩, G.not_isDiag_of_mem_edgeSet a.2⟩
  · intro he
    change e ∈ (matchingSubgraph G M).edgeSet at he
    rw [matchingSubgraph, SimpleGraph.edgeSet_fromEdgeSet] at he
    obtain ⟨⟨heG, heM⟩, _⟩ := he
    exact ⟨⟨e, heG⟩, heM, rfl⟩

lemma card_edgeFinset_matchingSubgraph (G : SimpleGraph V)
    (M : Finset G.edgeSet) :
    (matchingSubgraph G M).edgeFinset.card = M.card := by
  rw [← map_matchingSubgraph_eq_edgeFinset, Finset.card_map]

/-- Disjoint hypergraph supports force maximum graph degree one. -/
lemma matchingSubgraph_degree_le_one (G : SimpleGraph V) (M : Finset G.edgeSet)
    (hM : (graphHypergraph G).IsMatching M) (v : V) :
    (matchingSubgraph G M).degree v ≤ 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hxAdj : (matchingSubgraph G M).Adj v x := by simpa using hx
  have hyAdj : (matchingSubgraph G M).Adj v y := by simpa using hy
  have hxData : ∃ hxG : s(v, x) ∈ G.edgeSet,
      (⟨s(v, x), hxG⟩ : G.edgeSet) ∈ M := by
    change (∃ hxG : s(v, x) ∈ G.edgeSet,
      (⟨s(v, x), hxG⟩ : G.edgeSet) ∈ M) ∧ v ≠ x at hxAdj
    exact hxAdj.1
  have hyData : ∃ hyG : s(v, y) ∈ G.edgeSet,
      (⟨s(v, y), hyG⟩ : G.edgeSet) ∈ M := by
    change (∃ hyG : s(v, y) ∈ G.edgeSet,
      (⟨s(v, y), hyG⟩ : G.edgeSet) ∈ M) ∧ v ≠ y at hyAdj
    exact hyAdj.1
  obtain ⟨hxG, hxM⟩ := hxData
  obtain ⟨hyG, hyM⟩ := hyData
  by_contra hxy
  have hedge : s(v, x) ≠ s(v, y) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨_, hxy'⟩ | ⟨hvy, hxv⟩
    · exact hxy hxy'
    · exact hxy (hxv.trans hvy)
  have hdis := hM hxM hyM (fun h => hedge (Subtype.ext_iff.mp h))
  exact Finset.disjoint_left.mp hdis
    (show v ∈ (graphHypergraph G).support ⟨s(v, x), hxG⟩ by
      simp [graphHypergraph])
    (show v ∈ (graphHypergraph G).support ⟨s(v, y), hyG⟩ by
      simp [graphHypergraph])

/-- Every Pippenger--Spencer matching in the rank-two encoding is a linear
forest in the original graph. -/
lemma matchingSubgraph_linearForest (G : SimpleGraph V) (M : Finset G.edgeSet)
    (hM : (graphHypergraph G).IsMatching M) :
    LinearForest (matchingSubgraph G M) :=
  (MatchingGraph.of_degree_le_one
    (matchingSubgraph_degree_le_one G M hM)).linearForest

end PippengerSchedule

end

end Erdos622
