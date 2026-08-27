import Arxiv.Arxiv2411_18291.ExplicitBoostParameters
import Arxiv.Arxiv2411_18291.SharpComplementCliques
import Arxiv.Arxiv2411_18291.SharpFractionalBoostFromCounts

/-! # Fractional regularity boosting above an explicit threshold -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem fractional_boost_explicit (q r n : ℕ) (hqr : r + 1 < q)
    (hn : (4 * q) ^ (90 * q) ≤ n) (G : Hypergraph (Fin n) (r + 1))
    (hG : IsGraphBounded (complete (Fin n) (r + 1) \ G) (boostComplementBound q)) :
    ∃ p : Block (Fin n) q → ℝ, (∀ Q, 0 ≤ p Q ∧ p Q ≤ 1) ∧
      (∀ Q, ¬cliqueEdges (r + 1) Q ⊆ G → p Q = 0) ∧
      boundary (r + 1) p = fun e => if e ∈ G then
        ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2 else 0 := by
  have hq : 2 ≤ q := by omega
  have hnpos : 0 < n := by
    have hh := (boost_threshold_root_size_bounds hq hn).2.2
    omega
  obtain ⟨hθ, hε, hhalf, hcost, _, _⟩ := paper_boost_parameters q (r + 1) hqr
  have hnum := explicit_boost_count_numerics hqr hn
  apply exists_fractional_boost_of_mass_counts q r n hqr hnpos G hε.le hcost
  · intro e _
    simpa only [Fintype.card_fin] using rootedCliques_relative_error_of_complement_sum
      hG hθ.le hε.le (hhalf.trans (by norm_num))
      (by simpa only [Fintype.card_fin] using hnpos) e hqr.le
      (by simpa only [Fintype.card_fin] using hnum.1)
  · intro e _
    have hd : ((q + (r + 1) : ℕ) : ℝ) * (q + (r + 1) - (r + 1) : ℕ) +
        ((q + (r + 1)).choose (r + 1) : ℝ) * boostComplementBound q * Fintype.card (Fin n) ≤
          (1 / 2 : ℝ) * Fintype.card (Fin n) := by
      convert hnum.2 using 1 <;> simp only [Nat.add_sub_cancel_right, Fintype.card_fin]
      ring
    have hh := rootedCliques_relative_error_of_complement_sum (q := q + (r + 1))
      hG hθ.le (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      (by simpa only [Fintype.card_fin] using hnpos) e (by omega) hd
    simpa only [Fintype.card_fin, Nat.add_sub_cancel_right] using hh

end Arxiv2411_18291
