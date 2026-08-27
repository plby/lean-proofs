import Arxiv.Arxiv2411_18291.FiniteGoodDensity
import Arxiv.Arxiv2411_18291.FocusingParameters

/-! # Focusing candidate counts without an exponential constant loss -/

noncomputable section

namespace Arxiv2411_18291

theorem focusing_clique_mainTerm_lower_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card) :
    (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) * (n : ℝ) ^ (q - (r + 1)) ≤
      ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
        (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hp := good_reference_density_power_paper_threshold hqr hn
    (Nat.sub_le (q.choose (r + 1)) 1) K G hd hGK hloss
  have hm := mul_le_mul_of_nonneg_right
    (paper_factorial_margin_half_alpha hqr hn (Nat.sub_le q (r + 1)))
    (Real.rpow_nonneg hn0.le (-(paperAlpha q (r + 1) / 2)))
  rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hm
  have heq : (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) =
      ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ (q.choose (r + 1) - 1) *
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) := by
    rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add hn0]
    congr 1
    unfold paperFocusingExponent
    ring
  have hf : ((q - (r + 1)).factorial : ℝ) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) ≤ 1 / 8 := by nlinarith only [hm]
  have hprod := mul_le_mul_of_nonneg_right hf
    (pow_nonneg (Real.rpow_nonneg hn0.le (-paperAlpha q (r + 1))) (q.choose (r + 1) - 1))
  have hscalar : ((q - (r + 1)).factorial : ℝ) *
      (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) ≤
        (3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) := by
    rw [heq]
    have hnonneg := pow_nonneg (Real.rpow_nonneg hn0.le (-paperAlpha q (r + 1)))
      (q.choose (r + 1) - 1)
    nlinarith only [hprod, hp, hnonneg]
  apply (le_div_iff₀ (by exact_mod_cast Nat.factorial_pos (q - (r + 1)))).mpr
  have hh := mul_le_mul_of_nonneg_right hscalar (pow_nonneg hn0.le (q - (r + 1)))
  nlinarith only [hh]

theorem coloured_punctured_clique_count_paper_threshold
    {I : Type*} [Fintype I] {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (σ : I → Equiv.Perm (Fin n))
    (hcount : ∀ e : Block (Fin n) (r + 1),
      ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
        (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial ≤
          (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card)
    (e : Block (Fin n) (r + 1)) :
    (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) * (n : ℝ) ^ (q - (r + 1)) ≤
      (puncturedCliques (permutedUnion σ G) e q).card :=
  (focusing_clique_mainTerm_lower_paper_threshold hqr hn K G hd hGK hloss).trans
    ((hcount e).trans (Nat.cast_le.mpr
      (Finset.card_le_card (rainbowPuncturedCliques_subset_permutedUnion σ G e))))

end Arxiv2411_18291
