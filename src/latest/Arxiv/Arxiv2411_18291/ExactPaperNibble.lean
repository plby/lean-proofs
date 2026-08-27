import Arxiv.Arxiv2411_18291.SmallCliqueNibble
import Arxiv.Arxiv2411_18291.SixCliqueNibble

/-!
# The full Section 9 nibble at its original threshold and constant three

The pair case, logarithmic tracking for clique sizes three through five,
and the scaled comparison for larger cliques cover every positive rank.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_nibble_constant_three_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (φ τ : ℝ) (hG : (G.card : ℝ) = φ * (n.choose (r + 1) : ℝ))
    (hφ : (n : ℝ) ^ (-((r + 1 : ℕ) : ℝ) / 3) ≤ φ)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  by_cases hk6 : 6 ≤ q.choose (r + 1)
  · exact exists_sparse_nibble_of_six_le_clique_paper_threshold hqr hk6 hn hεhi
      G H φ τ hG hφ hτ hHG hd
  by_cases hq2 : q = 2
  · exact exists_sparse_nibble_paper_threshold_of_improved_parameters hqr hn hεhi
      (Or.inr (Or.inr (Or.inl hq2))) G H φ τ hG hφ hτ hHG hd
  have hq3 : 3 ≤ q := by omega
  have hk : 3 ≤ q.choose (r + 1) := by
    by_cases hr : 1 ≤ r
    · exact three_le_clique_size (by omega) hqr
    · have hr0 : r = 0 := by omega
      subst r
      simpa only [Nat.zero_add, Nat.choose_one_right] using hq3
  exact exists_sparse_nibble_of_small_clique_paper_threshold hqr hk (by omega) hn hεhi
    G H φ τ hG hφ hτ hHG hd

theorem exists_sparse_nibble_constant_three_all_positive_ranks {q r n : ℕ}
    (hr : 1 ≤ r) (hqr : r < q) (hn : paperSizeThreshold q r ≤ n)
    {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (G : Hypergraph (Fin n) r) (H : Finset (Block (Fin n) q))
    (φ τ : ℝ) (hG : (G.card : ℝ) = φ * (n.choose r : ℝ))
    (hφ : (n : ℝ) ^ (-(r : ℝ) / 3) ≤ φ)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges r Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - r) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - r) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport r C) C ∧
        ∀ S : Block (Fin n) (r - 1),
          (((G \ cliqueSupport r C).filter fun e => S.val ⊆ e.val).card : ℝ) <
            (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose r : ℝ))))) * n := by
  cases r with
  | zero => omega
  | succ r =>
    obtain ⟨C, hC, hdec, hbound⟩ :=
      exists_sparse_nibble_constant_three_paper_threshold hqr hn hεhi
        G H φ τ hG hφ hτ hHG hd
    refine ⟨C, hC, hdec, ?_⟩
    simpa only [IsGraphBounded, Nat.succ_sub_one, Fintype.card_fin] using hbound

end Arxiv2411_18291
