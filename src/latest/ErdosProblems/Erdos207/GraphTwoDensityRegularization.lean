/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GraphTriangleRegularization
import ErdosProblems.Erdos207.TwoDensityTriangleRegularization

/-! # Two-density regularization on the project's graph and typed-triple data -/

namespace Erdos207

open Finset

noncomputable section

theorem exists_graph_twoDensity_triangle_regularized
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (C p tau n eta : ℝ)
    (hC : 0 < C) (hp : 0 < p) (htau : 0 < tau) (hn : 0 < n)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G)
    (hdegree : ∀ e ∈ graphEdges G,
      |p ^ 2 * tau * n - (A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card| ≤
        p ^ 2 * tau * n / (12 * C ^ 5))
    (hext : ∀ S : Finset V, 2 ≤ S.card → S.card ≤ 4 → cliquePattern S ≤ G →
      p ^ S.card * tau ^ (S.card.choose 2) * n / C ≤
        ((properPatternExtensions A (cliquePattern S) univ).card : ℝ) ∧
      ((properPatternExtensions A (cliquePattern S) univ).card : ℝ) ≤
        C * p ^ S.card * tau ^ (S.card.choose 2) * n)
    (hfailure : 2 * (graphEdges G).card * Real.exp (-eta ^ 2 * (p ^ 2 * tau * n) / 16) < 1) :
    ∃ B ⊆ A, ∀ e ∈ graphEdges G,
      |((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) - p ^ 2 * tau * n / 4| ≤
        eta * (p ^ 2 * tau * n / 4) := by
  have hdeg : ∀ P ∈ graphPairFamily G,
      |p ^ 2 * tau * n - ((triangleVertexFamily A).filter (P ⊆ ·)).card| ≤
        p ^ 2 * tau * n / (12 * C ^ 5) := by
    intro P hP
    obtain ⟨e, he, rfl⟩ := mem_image.mp hP
    rw [triangleVertexFamily_edge_card A e (G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))]
    exact hdegree e he
  obtain ⟨R, hRA, hR⟩ := exists_twoDensity_triangle_regularized_finite
    (graphPairFamily G) (triangleVertexFamily A) C p tau n eta hC hp htau hn heta heta1
    (graphPairFamily_uniform G) (triangleVertexFamily_uniform A)
    (graphPairFamily_contains_triangle_pairs G A hA) hdeg
    (fun S hS2 hS4 hSG ↦ by
      rw [triangleSetExtensionVertices_eq_properPattern A S hS2]
      exact hext S hS2 hS4 ((cliquePattern_le_iff G S).mpr hSG))
    (by simpa only [graphPairFamily_card] using hfailure)
  obtain ⟨B, hBA, hBR⟩ := triangleVertexFamily_decode_subset A R hRA
  refine ⟨B, hBA, fun e he ↦ ?_⟩
  have hR' := hR e.toFinset ((mem_graphPairFamily_toFinset_iff G e).mpr he)
  rw [← hBR, triangleVertexFamily_edge_card B e
    (G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))] at hR'
  exact hR'

end

end Erdos207
