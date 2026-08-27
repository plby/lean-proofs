import Arxiv.Arxiv2411_18291.CliqueSquaredDegrees

/-! # Explicit one-step clique loss under degree control -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem cliqueNeighborhood_card_le_of_degree_bound (H : Finset (Block V q)) (D : ℝ)
    (hd : ∀ e : Block V r, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ D)
    (Q : Block V q) : (cliqueNeighborhood r H Q).card ≤ (q.choose r : ℝ) * D := by
  have h : ((cliqueNeighborhood r H Q).card : ℝ) ≤
      ∑ e ∈ cliqueEdges r Q, ((H.filter fun P => e.val ⊆ P.val).card : ℝ) := by
    exact_mod_cast cliqueNeighborhood_card_le_sum H Q
  calc
    _ ≤ _ := h
    _ ≤ ∑ _e ∈ cliqueEdges r Q, D := sum_le_sum fun e _ => hd e
    _ = _ := by simp [card_cliqueEdges]

omit [Fintype V] in
theorem clique_degree_bound_of_subset {H H₀ : Finset (Block V q)} (hH : H ⊆ H₀)
    (D : ℝ) (hd : ∀ e : Block V r, ((H₀.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ D)
    (e : Block V r) : ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ D := by
  have h : (H.filter fun Q => e.val ⊆ Q.val).card ≤
      (H₀.filter fun Q => e.val ⊆ Q.val).card := card_le_card (filter_subset_filter _ hH)
  exact (Nat.cast_le.mpr h).trans (hd e)

theorem cliqueRemoval_average_loss_of_degree_deviation (hqr : r < q)
    (G : Hypergraph V r) (hG : G.Nonempty) (H : Finset (Block V q)) (hH : H.Nonempty)
    (hHG : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) (m δ : ℝ)
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - m| ≤ δ) :
    let L := (∑ Q ∈ H, ((cliqueNeighborhood r H Q).card : ℝ)) / H.card
    (q.choose r : ℝ) ^ 2 * H.card / G.card -
        (q.choose r : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (q - r - 1) ≤ L ∧
      L ≤ (q.choose r : ℝ) ^ 2 * H.card / G.card + G.card * δ ^ 2 / H.card := by
  have hn : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  have hg : (0 : ℝ) < G.card := by exact_mod_cast hG.card_pos
  obtain ⟨hslo, hshi⟩ := clique_squared_degree_bounds G hG H hHG m δ hd
  obtain ⟨hlo, hhi⟩ := cliqueRemoval_average_loss_bounds hqr H hH
  have hid : ((H.card : ℝ) * q.choose r) ^ 2 / G.card / H.card =
      (q.choose r : ℝ) ^ 2 * H.card / G.card := by
    field_simp
  dsimp only at hlo hhi ⊢
  constructor
  · have h := sub_le_sub (div_le_div_of_nonneg_right hslo hn.le)
      (le_refl ((q.choose r : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (q - r - 1)))
    rw [hid] at h
    exact h.trans hlo
  · have h := div_le_div_of_nonneg_right hshi hn.le
    rw [add_div, hid] at h
    exact hhi.trans h

end Arxiv2411_18291
