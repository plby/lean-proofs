/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationTypical
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! # Exact edge-triangle double counting and regularized family mass -/

namespace Erdos207

open Finset

noncomputable section

theorem sum_graph_triangle_incidence
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : TripleSystemOn V)
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) :
    ∑ e ∈ graphEdges G, (A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card = 3 * A.card := by
  classical
  have hdouble := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := graphEdges G) (t := A) (fun e T ↦ e ∈ tripleEdgeFinset T)
  change (∑ e ∈ graphEdges G, (A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card) =
    ∑ T ∈ A, ((graphEdges G).filter (fun e ↦ e ∈ tripleEdgeFinset T)).card at hdouble
  rw [hdouble]
  have hfilter : ∀ T ∈ A, (graphEdges G).filter (fun e ↦ e ∈ tripleEdgeFinset T) = tripleEdgeFinset T := by
    intro T hT
    ext e
    simp only [mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hA T hT h, h⟩⟩
  calc
    _ = ∑ T ∈ A, (tripleEdgeFinset T).card := sum_congr rfl (fun T hT ↦ congrArg Finset.card (hfilter T hT))
    _ = _ := by simp [card_tripleEdgeFinset, mul_comm]

theorem triangle_family_mass_of_regular_degrees
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : TripleSystemOn V)
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) (mu eta : ℝ)
    (hmu : 0 ≤ mu) (heta : eta ≤ 1 / 2)
    (hdegree : ∀ e ∈ graphEdges G,
      |((A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) - mu| ≤ eta * mu) :
    (graphEdges G).card * mu / 6 ≤ (A.card : ℝ) := by
  have hpoint : ∀ e ∈ graphEdges G, mu / 2 ≤ ((A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) := by
    intro e he
    have hlower := (abs_le.mp (hdegree e he)).1
    have herror := mul_le_mul_of_nonneg_right heta hmu
    linarith
  have hsum : (graphEdges G).card * (mu / 2) ≤ 3 * (A.card : ℝ) := by
    calc
      _ = ∑ _e ∈ graphEdges G, mu / 2 := by simp
      _ ≤ ∑ e ∈ graphEdges G, ((A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) := sum_le_sum hpoint
      _ = _ := by exact_mod_cast sum_graph_triangle_incidence G A hA
  linarith

end

end Erdos207
