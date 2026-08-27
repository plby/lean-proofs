import Arxiv.Arxiv2411_18291.ConstantComplementFractionalBoost
import Arxiv.Arxiv2411_18291.RegularityBoost
import Arxiv.Arxiv2411_18291.PaperFractionalBoost
import Arxiv.Arxiv2411_18291.ExplicitRegularityBoost

/-!
# Regularity boosting with a constant complement bound

The printed complement bound `2^(-3q)` works for all sufficiently large
vertex sets. The output has the binomial main term and the stronger relative
error required by the nibble. The specific binomial conclusion is now a
corollary of the finite theorem above the printed size threshold.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_regular_clique_family_paper_constant_power_scale
    (q r : ℕ) (hqr : r + 1 < q) {κ : ℝ} (hκ : 0 ≤ κ) (hκhalf : κ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) (boostComplementBound q) →
      ∃ H : Finset (Block (Fin n) q), H ⊆ cliqueFamily G q ∧ ∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2| ≤
            (n : ℝ) ^ (-κ) * (((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2) := by
  have hfrac := eventually_fractional_boost_paper_constant q r hqr
  filter_upwards [hfrac,
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

theorem eventually_regularity_boost_paper_constant (q r : ℕ) (hqr : r + 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) (boostComplementBound q) →
      ∃ H : Finset (Block (Fin n) q), H ⊆ cliqueFamily G q ∧ ∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n.choose (q - (r + 1)) : ℝ) / 2| ≤
          (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n.choose (q - (r + 1)) : ℝ) / 2) := by
  filter_upwards [eventually_ge_atTop ((4 * q) ^ (90 * q))] with n hn
  intro G hG
  exact regularity_boost_explicit q r n hqr hn G hG

theorem exists_constant_complement_regular_clique_family_power_scale
    (q r : ℕ) (hqr : r + 1 < q) {κ : ℝ} (hκ : 0 ≤ κ) (hκhalf : κ < 1 / 2) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) θ →
      ∃ H : Finset (Block (Fin n) q), H ⊆ cliqueFamily G q ∧ ∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2| ≤
            (n : ℝ) ^ (-κ) * (((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2) := by
  exact ⟨boostComplementBound q, by unfold boostComplementBound; positivity,
    eventually_regular_clique_family_paper_constant_power_scale q r hqr hκ hκhalf⟩

theorem exists_constant_complement_regularity_boost (q r : ℕ) (hqr : r + 1 < q) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) θ →
      ∃ H : Finset (Block (Fin n) q), H ⊆ cliqueFamily G q ∧ ∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n.choose (q - (r + 1)) : ℝ) / 2| ≤
          (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n.choose (q - (r + 1)) : ℝ) / 2) := by
  exact ⟨boostComplementBound q, by unfold boostComplementBound; positivity,
    eventually_regularity_boost_paper_constant q r hqr⟩

end Arxiv2411_18291
