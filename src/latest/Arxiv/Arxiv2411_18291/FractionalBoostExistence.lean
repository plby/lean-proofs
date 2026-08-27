import Arxiv.Arxiv2411_18291.FractionalBoostFromCounts
import Arxiv.Arxiv2411_18291.AsymptoticNearCompleteCliques

/-!
# Fractional regularization for graphs with sparse complement

Construct valid clique sampling probabilities with exactly the same edge
mean. All decoding sets are actual graph cliques. Polynomially small
complement degrees make the explicit coefficient correction tend to zero.
Independent sampling and its simultaneous concentration remain separate.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_exists_fractional_boost (q r : ℕ) (hqr : r + 1 ≤ q)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) ((n : ℝ) ^ (-δ)) →
      ∃ p : Block (Fin n) q → ℝ, (∀ Q, 0 ≤ p Q ∧ p Q ≤ 1) ∧
        (∀ Q, ¬cliqueEdges (r + 1) Q ⊆ G → p Q = 0) ∧
        boundary (r + 1) p = fun e => if e ∈ G then
          ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2 else 0 := by
  have hκ := half_pos hδ
  have hκδ : δ / 2 < δ := by linarith only [hδ]
  have hκ1 : δ / 2 < 1 := by linarith only [hδ1]
  have hlim := (tendsto_rpow_neg_atTop hκ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  let K := fractionalBoostConstant q (r + 1)
  filter_upwards [eventually_rootedClique_count_of_bounded_complement q r (r + 1)
      hqr hκ hκδ hκ1,
    eventually_rootedClique_count_of_bounded_complement (q + (r + 1)) r (r + 1)
      (by omega) hκ hκδ hκ1,
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    (hlim.const_mul K).eventually (gt_mem_nhds (by simp : K * 0 < 1 / 2)),
    eventually_ge_atTop (1 : ℕ)] with n hcount hdecode hhalf hcost hn
  intro G hG
  apply exists_fractional_boost_of_relative_counts q r n hqr (by omega) G
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hhalf.le hcost.le
  · intro e _
    exact hcount G hG e
  · intro e _
    simpa only [Nat.add_sub_cancel_right] using hdecode G hG e

end Arxiv2411_18291
