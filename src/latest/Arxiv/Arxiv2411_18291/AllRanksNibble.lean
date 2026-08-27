import Arxiv.Arxiv2411_18291.GeneralPairNibble
import Arxiv.Arxiv2411_18291.NibbleNonPairRanks
import Arxiv.Arxiv2411_18291.FiniteGeneralNibble

/-! # General eventual nibble in every positive rank -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_exists_nibble_all_ranks_pos (q r : ℕ) (hqr : r + 1 < q)
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
  by_cases hfinite :
      (3 * (q.choose (r + 1) : ℝ) * paperRho q (r + 1) ≤ ε ∨ q = 2 ∨
        15 ≤ q.choose (r + 1)) ∧ ε ≤ 2 / 5
  · filter_upwards [eventually_ge_atTop (paperSizeThreshold q (r + 1))] with n hn
    exact exists_sparse_nibble_paper_threshold_of_covered_parameters
      hqr hn hfinite.2 (Or.inr hfinite.1)
  · by_cases hq : 3 ≤ q
    · exact eventually_exists_nibble_of_three_le_q q r hq hqr hε hεhalf
    · have hq2 : q = 2 := by omega
      have hr0 : r = 0 := by omega
      subst q r
      norm_num only [Nat.zero_add, Nat.reduceSub, Nat.choose_one_right, Nat.cast_one,
        Nat.cast_ofNat, neg_div]
      filter_upwards [eventually_exists_general_pair_nibble hε hεhalf,
        eventually_ge_atTop (1 : ℕ)] with n hn hn1
      intro G H φ τ hG hφ hτ hHG hd
      apply hn G H τ _ hτ hHG hd
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hp : (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (-(1 / 3 : ℝ)) * n := by
        rw [show (2 / 3 : ℝ) = -(1 / 3 : ℝ) + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
      rw [hp, hG]
      exact mul_le_mul_of_nonneg_right hφ hn0.le

/-- The nonpositive-error range is trivial, so no lower bound on `ε` is needed. -/
theorem eventually_exists_nibble_all_ranks (q r : ℕ) (hqr : r + 1 < q)
    {ε : ℝ} (hεhalf : ε < 1 / 2) :
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
  by_cases hε : 0 < ε
  · exact eventually_exists_nibble_all_ranks_pos q r hqr hε hεhalf
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    intro G H φ τ _ _ _ _ _
    exact exists_nibble_of_nonpositive_error hn (le_of_not_gt hε) G H

end Arxiv2411_18291
