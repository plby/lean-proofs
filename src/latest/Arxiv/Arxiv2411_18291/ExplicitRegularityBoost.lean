import Arxiv.Arxiv2411_18291.ExplicitFractionalBoost
import Arxiv.Arxiv2411_18291.ExplicitCliqueSampling
import Arxiv.Arxiv2411_18291.ExplicitBoostBinomial
import Arxiv.Arxiv2411_18291.RegularityBoost

/-!
# Regularity boosting at the printed threshold

The construction in fact works already for `n >= (4q)^(90q)`. It retains
the printed complement constant and gives stronger relative output error.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem regular_clique_family_explicit_power_scale (q r n : ℕ) (hqr : r + 1 < q)
    (hn : (4 * q) ^ (90 * q) ≤ n) (G : Hypergraph (Fin n) (r + 1))
    (hG : IsGraphBounded (complete (Fin n) (r + 1) \ G) (boostComplementBound q)) :
    ∃ H : Finset (Block (Fin n) q), H ⊆ cliqueFamily G q ∧ ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2| ≤
          (n : ℝ) ^ (-(2 / 5 : ℝ)) *
            (((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2) := by
  have hq : 2 ≤ q := by omega
  obtain ⟨p, hp, hs, hboundary⟩ := fractional_boost_explicit q r n hqr hn G hG
  have hcard : (G.card : ℝ) ≤ n.choose (r + 1) := by
    have hh := card_le_card (subset_univ G)
    simpa only [card_univ, Block, Fintype.card_finset_len, Fintype.card_fin] using
      (Nat.cast_le (α := ℝ)).mpr hh
  let c : ℝ := (n : ℝ) ^ (-(2 / 5 : ℝ))
  let μ : ℝ := ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) / 2
  have hfail := clique_sampling_failure_explicit hq hqr.le (Nat.sub_le q (r + 1))
    (by omega : 1 ≤ q - (r + 1)) hn
  have hsmall : (G.card : ℝ) * (2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c))))) < 1 :=
    (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_lt hfail
  exact exists_clique_family_from_fractional G p hp hs hboundary
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hsmall

theorem regularity_boost_explicit (q r n : ℕ) (hqr : r + 1 < q)
    (hn : (4 * q) ^ (90 * q) ≤ n) (G : Hypergraph (Fin n) (r + 1))
    (hG : IsGraphBounded (complete (Fin n) (r + 1) \ G) (boostComplementBound q)) :
    ∃ H : Finset (Block (Fin n) q), H ⊆ cliqueFamily G q ∧ ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n.choose (q - (r + 1)) : ℝ) / 2| ≤
        (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n.choose (q - (r + 1)) : ℝ) / 2) := by
  obtain ⟨H, hH, hcounts⟩ := regular_clique_family_explicit_power_scale q r n hqr hn G hG
  obtain ⟨hsmall, hscale, hchoose⟩ := explicit_boost_binomial_numerics (by omega : 2 ≤ q) hn
  refine ⟨H, hH, fun e he => ?_⟩
  have hlo : (1 - (n : ℝ) ^ (-(2 / 5 : ℝ))) *
      ((n : ℝ) ^ (q - (r + 1)) / (q - (r + 1)).factorial) ≤
        (n.choose (q - (r + 1)) : ℝ) := by
    simpa only [mul_div_assoc] using hchoose (q - (r + 1)) (Nat.sub_le _ _)
  have hη : 2 * (n : ℝ) ^ (-(2 / 5 : ℝ)) ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) / 2 := by
    linarith only [hscale]
  have hh := regular_count_change_scale (Real.rpow_nonneg (Nat.cast_nonneg n) _) hsmall
    (Nat.cast_nonneg _) (hcounts e he) hlo
    (by simpa only [Nat.sub_zero] using shifted_choose_upper n 0 (q - (r + 1))) hη
  convert hh using 1
  ring

/-- The full Boost lemma at the printed size bound, with stronger relative error. -/
theorem regularity_boost_paper_threshold (q r n : ℕ) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (G : Hypergraph (Fin n) (r + 1))
    (hG : IsGraphBounded (complete (Fin n) (r + 1) \ G) (boostComplementBound q)) :
    ∃ H : Finset (Block (Fin n) q), H ⊆ cliqueFamily G q ∧ ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n.choose (q - (r + 1)) : ℝ) / 2| ≤
        (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n.choose (q - (r + 1)) : ℝ) / 2) :=
  regularity_boost_explicit q r n hqr ((boost_threshold_le_paper_threshold hqr).trans hn) G hG

end Arxiv2411_18291
