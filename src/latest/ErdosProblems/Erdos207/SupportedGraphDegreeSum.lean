/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CliquePatternTypicality
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Degree double counting on the actual graph support -/

namespace Erdos207

open Finset

noncomputable section

theorem neighborsIn_eq_neighborFinset_of_supported
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (hG : GraphSupportedOn G (D : Set V)) (v : V) :
    neighborsIn G D v = G.neighborFinset v := by
  ext w
  simp only [mem_neighborsIn_iff, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨(hG h).2, h⟩⟩

theorem sum_neighborsIn_card_eq_twice_edges
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (D : Finset V) (hG : GraphSupportedOn G (D : Set V)) :
    ∑ v ∈ D, (neighborsIn G D v).card = 2 * (graphEdges G).card := by
  classical
  simp_rw [neighborsIn_eq_neighborFinset_of_supported G D hG, SimpleGraph.card_neighborFinset_eq_degree]
  rw [graphEdges_eq_edgeFinset]
  apply Eq.trans _ G.sum_degrees_eq_twice_card_edges
  apply sum_subset (subset_univ D)
  intro v _hv hvD
  rw [← G.card_neighborFinset_eq_degree]
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  exact hvD (hG ((G.mem_neighborFinset v w).mp hw)).1

theorem graphEdges_mass_of_neighbor_lower
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (D : Finset V) (hG : GraphSupportedOn G (D : Set V)) (p : ℝ)
    (hdegree : ∀ v ∈ D, p * D.card / 2 ≤ (neighborsIn G D v).card) :
    p * (D.card : ℝ) ^ 2 / 4 ≤ (graphEdges G).card := by
  have hs : (D.card : ℝ) * (p * D.card / 2) ≤ 2 * (graphEdges G).card := by
    calc
      _ = ∑ _v ∈ D, p * D.card / 2 := by simp
      _ ≤ ∑ v ∈ D, ((neighborsIn G D v).card : ℝ) := sum_le_sum hdegree
      _ = _ := by exact_mod_cast sum_neighborsIn_card_eq_twice_edges G D hG
  nlinarith

end

end Erdos207
