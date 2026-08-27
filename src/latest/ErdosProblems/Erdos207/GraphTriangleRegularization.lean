/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CliquePatternExtensions

/-! # Source triangle regularization on the project's graph and triple types -/

namespace Erdos207

open Finset

noncomputable section

theorem graph_triangle_regularization_with_edge_count :
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n →
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
      ∀ (G : SimpleGraph V) (A : TripleSystemOn V) (C p : ℝ),
      (graphEdges G).card ≤ n ^ 2 →
      2 ≤ C → (n : ℝ) ^ (-1 / 6 : ℝ) < p → p < 1 →
      (∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) →
      (∀ e ∈ graphEdges G,
        |p ^ 2 * n - (A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card| ≤
          p ^ 2 * n / (12 * C ^ 5)) →
      (∀ S : Finset V, 2 ≤ S.card → S.card ≤ 4 → cliquePattern S ≤ G →
        p ^ S.card * n / C ≤ ((properPatternExtensions A (cliquePattern S) univ).card : ℝ) ∧
          ((properPatternExtensions A (cliquePattern S) univ).card : ℝ) ≤ C * p ^ S.card * n) →
      ∃ B ⊆ A, ∀ e ∈ graphEdges G,
        |((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) - p ^ 2 * n / 4| ≤
          (n : ℝ) ^ (-1 / 4 : ℝ) * (p ^ 2 * n / 4) := by
  obtain ⟨N, hN⟩ := source_triangle_regularization_with_edge_count
  refine ⟨N, fun n hn V _ _ G A C p hcard hC hp hp1 hA hdegree hext ↦ ?_⟩
  have hdeg : ∀ P ∈ graphPairFamily G,
      |p ^ 2 * n - ((triangleVertexFamily A).filter (P ⊆ ·)).card| ≤ p ^ 2 * n / (12 * C ^ 5) := by
    intro P hP
    obtain ⟨e, he, rfl⟩ := mem_image.mp hP
    rw [triangleVertexFamily_edge_card A e (G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))]
    exact hdegree e he
  have hext' : ∀ S : Finset V, 2 ≤ S.card → S.card ≤ 4 → S.powersetCard 2 ⊆ graphPairFamily G →
      p ^ S.card * n / C ≤ ((triangleSetExtensionVertices (triangleVertexFamily A) S).card : ℝ) ∧
        ((triangleSetExtensionVertices (triangleVertexFamily A) S).card : ℝ) ≤ C * p ^ S.card * n := by
    intro S hS2 hS4 hSG
    rw [triangleSetExtensionVertices_eq_properPattern A S hS2]
    exact hext S hS2 hS4 ((cliquePattern_le_iff G S).mpr hSG)
  obtain ⟨R, hRA, hR⟩ := hN n hn (graphPairFamily G) (triangleVertexFamily A) C p
    (by simpa only [graphPairFamily_card] using hcard) hC hp hp1
    (graphPairFamily_uniform G) (triangleVertexFamily_uniform A)
    (graphPairFamily_contains_triangle_pairs G A hA) hdeg hext'
  obtain ⟨B, hBA, hBR⟩ := triangleVertexFamily_decode_subset A R hRA
  refine ⟨B, hBA, fun e he ↦ ?_⟩
  have hR' := hR e.toFinset ((mem_graphPairFamily_toFinset_iff G e).mpr he)
  rw [← hBR, triangleVertexFamily_edge_card B e
    (G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))] at hR'
  exact hR'

theorem graph_triangle_regularization :
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n →
      ∀ {V : Type*} [Fintype V] [DecidableEq V], Fintype.card V = n →
      ∀ (G : SimpleGraph V) (A : TripleSystemOn V) (C p : ℝ),
      2 ≤ C → (n : ℝ) ^ (-1 / 6 : ℝ) < p → p < 1 →
      (∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) →
      (∀ e ∈ graphEdges G,
        |p ^ 2 * n - (A.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card| ≤
          p ^ 2 * n / (12 * C ^ 5)) →
      (∀ S : Finset V, 2 ≤ S.card → S.card ≤ 4 → cliquePattern S ≤ G →
        p ^ S.card * n / C ≤ ((properPatternExtensions A (cliquePattern S) univ).card : ℝ) ∧
          ((properPatternExtensions A (cliquePattern S) univ).card : ℝ) ≤ C * p ^ S.card * n) →
      ∃ B ⊆ A, ∀ e ∈ graphEdges G,
        |((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) - p ^ 2 * n / 4| ≤
          (n : ℝ) ^ (-1 / 4 : ℝ) * (p ^ 2 * n / 4) := by
  obtain ⟨N, hN⟩ := graph_triangle_regularization_with_edge_count
  refine ⟨N, fun n hn V _ _ hV G A C p hC hp hp1 hA hdegree hext ↦ ?_⟩
  have hcard := graphEdges_card_le_support_sq G univ (fun _ _ _ ↦ ⟨mem_univ _, mem_univ _⟩)
  simp only [card_univ, hV] at hcard
  exact hN n hn G A C p hcard hC hp hp1 hA hdegree hext

end

end Erdos207
