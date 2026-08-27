/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborMoments
import ErdosProblems.Erdos207.InitialResidualPairs
import ErdosProblems.Erdos207.IterationTypical

/-! # Identifying the auxiliary neighbor statistic with the actual residual graph -/

namespace Erdos207

open Finset

noncomputable section

theorem pair_mem_initialResidualPairs_iff
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (v u : V) :
    ({v, u} : Finset V) ∈ initialResidualPairs H ↔ v ≠ u ∧ ¬ H.Adj v u := by
  rw [mem_initialResidualPairs]
  constructor
  · rintro ⟨hcard, havoid⟩
    have hne : v ≠ u := by intro heq; subst u; simp at hcard
    exact ⟨hne, havoid v (by simp) u (by simp) hne⟩
  · rintro ⟨hne, havoid⟩
    refine ⟨by simp [hne], ?_⟩
    intro a ha b hb hab
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact havoid
    · exact fun hadj ↦ havoid hadj.symm
    · exact (hab rfl).elim

theorem pairUncovered_pair_iff_not_covered_adj
    {V : Type*} [Fintype V] [DecidableEq V] (S : GreedyStateOn V) {v u : V} (hvu : v ≠ u) :
    PairUncovered {v, u} S ↔ ¬ (coveredGraph S.chosen).Adj v u := by
  simp [PairUncovered, mem_chosenPairFinsets_iff, coveredGraph_adj, hvu,
    insert_subset_iff, singleton_subset_iff]

theorem uncoveredNeighbors_initialResidualPairs_eq_graph_neighbors
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (U : Finset V) (v : V)
    (S : GreedyStateOn V) :
    uncoveredNeighbors (initialResidualPairs H) U v S =
      neighborsIn (graphDifference (graphDifference (SimpleGraph.completeGraph V) H)
        (coveredGraph S.chosen)) U v := by
  ext u
  rw [mem_neighborsIn_iff]
  by_cases hvu : v = u
  · subst u
    simp [uncoveredNeighbors]
  · have hpair := pair_mem_initialResidualPairs_iff H v u
    have huncovered := pairUncovered_pair_iff_not_covered_adj S hvu
    simp only [uncoveredNeighbors, mem_filter]
    change (u ∈ U ∧ u ≠ v ∧ {v, u} ∈ initialResidualPairs H ∧ PairUncovered {v, u} S) ↔
      u ∈ U ∧ ((v ≠ u ∧ v ≠ u ∧ ¬ H.Adj v u) ∧ v ≠ u ∧ ¬ (coveredGraph S.chosen).Adj v u)
    rw [hpair, huncovered]
    simp [hvu, Ne.symm hvu]

end

end Erdos207
