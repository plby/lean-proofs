import Arxiv.Arxiv2411_18291.SparseRankOneNibble
import Arxiv.Arxiv2411_18291.AsymptoticNibble

/-! # General eventual nibble for every clique size at least three -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_exists_nibble_of_three_le_q (q r : ℕ) (hq : 3 ≤ q) (hqr : r + 1 < q)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
      (φ τ : ℝ), (G.card : ℝ) = φ * (n.choose (r + 1) : ℝ) →
      (n : ℝ) ^ (-((r + 1 : ℕ) : ℝ) / 3) ≤ φ → (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ →
      (∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) →
      (∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
          (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) →
      ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
        IsDecomposition (cliqueSupport (r + 1) C) C ∧
          IsGraphBounded (G \ cliqueSupport (r + 1) C)
            (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  by_cases hr : 1 ≤ r
  · exact eventually_exists_nibble q r hr hqr hε hεhalf
  · have hr0 : r = 0 := by omega
    subst r
    simp only [Nat.zero_add, Nat.choose_one_right, Nat.cast_one, neg_div]
    filter_upwards [eventually_exists_sparse_rankOne_nibble q hq hε hεhalf,
      eventually_ge_atTop (1 : ℕ)] with n hn hn1
    intro G H φ τ hG hφ hτ hHG hd
    apply hn G H τ _ hτ hHG hd
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hp : (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (-(1 / 3 : ℝ)) * n := by
      rw [show (2 / 3 : ℝ) = -(1 / 3 : ℝ) + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
    rw [hp, hG]
    exact mul_le_mul_of_nonneg_right hφ hn0.le

end Arxiv2411_18291
