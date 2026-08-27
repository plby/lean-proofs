import Arxiv.Arxiv2411_18291.FractionalBoostExistence
import Arxiv.Arxiv2411_18291.FractionalCliqueSampling
import Arxiv.Arxiv2411_18291.CliqueSamplingNumerics

/-!
# An actual regular clique family in a graph with sparse complement

Construct the fractional probabilities, then sample them independently.
For any relative exponent below one half, all graph edges simultaneously
have the required clique count. The current main term is `n^(q-r)/(2*(q-r)!)`.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_exists_regular_clique_family_power_scale (q r : ℕ) (hqr : r + 1 < q)
    {δ κ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hκ : 0 ≤ κ) (hκhalf : κ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) ((n : ℝ) ^ (-δ)) →
      ∃ H : Finset (Block (Fin n) q), H ⊆ cliqueFamily G q ∧ ∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2| ≤
            (n : ℝ) ^ (-κ) * (((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2) := by
  filter_upwards [eventually_exists_fractional_boost q r hqr.le hδ hδ1,
    eventually_clique_sampling_failure_lt_one (r + 1) (q - (r + 1))
      (by omega) hκ hκhalf] with n hfrac hfail
  intro G hG
  obtain ⟨p, hp, hs, hboundary⟩ := hfrac G hG
  have hcard : (G.card : ℝ) ≤ n.choose (r + 1) := by
    have hh := card_le_card (subset_univ G)
    simpa only [card_univ, Block, Fintype.card_finset_len, Fintype.card_fin] using
      (Nat.cast_le (α := ℝ)).mpr hh
  have hsmall : (G.card : ℝ) *
      (2 * Real.exp (-((((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2) *
        ((n : ℝ) ^ (-κ)) ^ 2 / (2 * (1 + 2 * (n : ℝ) ^ (-κ)))))) < 1 :=
    (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_lt hfail
  exact exists_clique_family_from_fractional G p hp hs hboundary
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hsmall

end Arxiv2411_18291
