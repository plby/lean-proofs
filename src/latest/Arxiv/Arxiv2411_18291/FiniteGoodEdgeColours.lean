import Arxiv.Arxiv2411_18291.FinitePermutationPairs
import Arxiv.Arxiv2411_18291.TypicalGoodEdgeColours

/-! # Finite marginal and joint colour estimates for the good graph -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem good_edge_colour_estimates_paper_threshold {q r n h : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hqh : q.choose (r + 1) ≤ h)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card) :
    (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ≤ density G ∧
      (1 - (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) * density K ≤ density G ∧
      ∀ [MeasurableSpace (Equiv.Perm (Fin n))]
        [MeasurableSingletonClass (Equiv.Perm (Fin n))],
      ∀ j < r + 1, ∀ P : IntersectingBlockPair (Fin n) (r + 1) (r + 1) j,
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
          {σ | P.val.1 ∈ mapGraph σ.toEmbedding G ∧ P.val.2 ∈ mapGraph σ.toEmbedding G} ≤
          (1 + (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12))) * density K ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hα := paperAlpha_pos hqr
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  refine ⟨good_reference_density_lower_paper_threshold hqr hn K G hd hGK hloss, ?_, ?_⟩
  · have he := Real.rpow_le_rpow_of_exponent_le hn1
      (by linarith only [hα] : -(paperAlpha q (r + 1) / 10) ≤ -(paperAlpha q (r + 1) / 12))
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_left he 1) (density_nonneg K)).trans
      (density_good_lower hGK hloss)
  · intro _ _ j hj P
    have hG : G ⊆ cliqueFamily K (r + 1) := by rw [cliqueFamily_self]; exact hGK
    have hp := permuted_clique_pair_probability_paper_threshold hqr hn hqr.le hqh
      K hT hd P hj G G hG hG
    simp only [Nat.choose_self, mul_one] at hp
    have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 2)
      (t := (1 / 12 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
    have hc : (16 : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 12) := by
      have hh : (16 : ℝ) ≤ (4 * q : ℝ) ^ 2 := by nlinarith only [hq]
      simpa only [div_eq_mul_inv, one_mul] using hh.trans hg
    have hm := mul_le_mul_of_nonneg_right hc
      (Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 6)))
    have heq : (n : ℝ) ^ (paperAlpha q (r + 1) / 12) *
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 6)) =
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 12)) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    rw [heq] at hm
    exact hp.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl hm) (sq_nonneg _))

end Arxiv2411_18291
