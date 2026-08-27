import Arxiv.Arxiv2411_18291.CliqueRemovalDrift
import Arxiv.Arxiv2411_18291.FiniteSquaredDeviation

/-! # The sum of squared clique degrees on the remaining graph -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem clique_degree_zero_outside_graph (G : Hypergraph V r) (H : Finset (Block V q))
    (hH : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) (e : Block V r) (he : e ∉ G) :
    (H.filter fun Q => e.val ⊆ Q.val).card = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro Q hQ
  obtain ⟨hQH, heQ⟩ := mem_filter.mp hQ
  exact he (hH Q hQH ((mem_cliqueEdges e Q).mpr heQ))

theorem sum_clique_degree_over_graph (G : Hypergraph V r) (H : Finset (Block V q))
    (hH : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) :
    (∑ e ∈ G, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ)) =
      (H.card : ℝ) * q.choose r := by
  have hu : (∑ e : Block V r, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ)) =
      (H.card : ℝ) * q.choose r := by
    simpa [card_cliqueEdges] using
      (sum_clique_family_edge_weights H (fun _ : Block V r => (1 : ℝ))).symm
  rw [← hu]
  apply sum_subset (subset_univ _)
  intro e _ he
  rw [clique_degree_zero_outside_graph G H hH e he, Nat.cast_zero]

theorem sum_sq_clique_degree_over_graph (G : Hypergraph V r) (H : Finset (Block V q))
    (hH : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) :
    (∑ e ∈ G, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ^ 2) =
      ∑ e : Block V r, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ^ 2 := by
  apply sum_subset (subset_univ _)
  intro e _ he
  rw [clique_degree_zero_outside_graph G H hH e he, Nat.cast_zero, zero_pow (by decide)]

theorem clique_squared_degree_bounds (G : Hypergraph V r) (hG : G.Nonempty)
    (H : Finset (Block V q)) (hH : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) (m δ : ℝ)
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - m| ≤ δ) :
    ((H.card : ℝ) * q.choose r) ^ 2 / G.card ≤
        (∑ e : Block V r, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ^ 2) ∧
      (∑ e : Block V r, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ^ 2) ≤
        ((H.card : ℝ) * q.choose r) ^ 2 / G.card + G.card * δ ^ 2 := by
  let d : Block V r → ℝ := fun e => (H.filter fun Q => e.val ⊆ Q.val).card
  have h := finite_sum_sq_bounds_of_deviation G hG d m δ hd
  change (∑ e ∈ G, d e) ^ 2 / (G.card : ℝ) ≤ (∑ e ∈ G, d e ^ 2) ∧
    (∑ e ∈ G, d e ^ 2) ≤ (∑ e ∈ G, d e) ^ 2 / (G.card : ℝ) + G.card * δ ^ 2 at h
  dsimp only [d] at h
  rw [sum_clique_degree_over_graph G H hH, sum_sq_clique_degree_over_graph G H hH] at h
  exact h

end Arxiv2411_18291
