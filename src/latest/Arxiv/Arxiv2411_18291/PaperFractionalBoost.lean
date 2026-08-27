import Arxiv.Arxiv2411_18291.ExplicitFractionalBoost

/-! # Fractional regularity boosting at the printed complement constant -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_fractional_boost_paper_constant (q r : ℕ) (hqr : r + 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) (boostComplementBound q) →
      ∃ p : Block (Fin n) q → ℝ, (∀ Q, 0 ≤ p Q ∧ p Q ≤ 1) ∧
        (∀ Q, ¬cliqueEdges (r + 1) Q ⊆ G → p Q = 0) ∧
        boundary (r + 1) p = fun e => if e ∈ G then
          ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2 else 0 := by
  filter_upwards [eventually_ge_atTop ((4 * q) ^ (90 * q))] with n hn
  intro G hG
  exact fractional_boost_explicit q r n hqr hn G hG

end Arxiv2411_18291
