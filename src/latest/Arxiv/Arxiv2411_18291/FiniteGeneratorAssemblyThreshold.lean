import Arxiv.Arxiv2411_18291.FiniteDecoderAugmentation

/-! # An explicit assembly threshold for arbitrary fixed generator coefficients -/

noncomputable section

namespace Arxiv2411_18291

def finiteGeneratorAssemblyThreshold (q r : ℕ) (C : ℝ) : ℕ :=
  max (paperSizeThreshold q (r + 1))
    (⌈max 1 C⌉₊ ^ (20 * paperInverseAlpha q (r + 1)))

theorem generator_coefficient_le_twentieth_alpha {q r n : ℕ} (hqr : r + 1 < q)
    {C : ℝ} (hn : finiteGeneratorAssemblyThreshold q r C ≤ n) :
    C ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 20) := by
  have hT : (⌈max 1 C⌉₊ ^ (20 * paperInverseAlpha q (r + 1)) : ℕ) ≤ n :=
    (le_max_right _ _).trans hn
  have hg := Real.rpow_le_rpow
    (Nat.cast_nonneg (⌈max 1 C⌉₊ ^ (20 * paperInverseAlpha q (r + 1))))
    (by exact_mod_cast hT :
      ((⌈max 1 C⌉₊ ^ (20 * paperInverseAlpha q (r + 1)) : ℕ) : ℝ) ≤ n)
    (div_nonneg (paperAlpha_pos hqr).le (by norm_num : (0 : ℝ) ≤ 20))
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _)] at hg
  have hexp : ((20 * paperInverseAlpha q (r + 1) : ℕ) : ℝ) *
      (paperAlpha q (r + 1) / 20) = 1 := by
    push_cast
    calc
      _ = paperAlpha q (r + 1) * paperInverseAlpha q (r + 1) := by ring
      _ = 1 := paperAlpha_mul_inverse hqr
  rw [hexp, Real.rpow_one] at hg
  exact (le_max_right 1 C).trans ((Nat.le_ceil (max 1 C)).trans hg)

theorem generator_input_normalization_explicit {q r n : ℕ} (hqr : r + 1 < q)
    {C : ℝ} (hn : finiteGeneratorAssemblyThreshold q r C ≤ n) :
    C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) ≤
      (n : ℝ) ^ (-(13 * paperAlpha q (r + 1) / 20)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans
      ((paperSizeThreshold_one_lt hqr).trans_le ((le_max_left _ _).trans hn))
  calc
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 20) *
        (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) :=
      mul_le_mul_of_nonneg_right (generator_coefficient_le_twentieth_alpha hqr hn)
        (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

theorem normalized_decoder_cost_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (1 + q.choose (r + 1) *
      (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1))) *
        (2 * (n : ℝ) ^ (-(13 * paperAlpha q (r + 1) / 20))) ≤
      (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hK : (1 + q.choose (r + 1) *
      (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) : ℝ) ≤
      (4 * q : ℝ) ^ (2 * q + 1) := by
    exact_mod_cast decoder_augmentation_coefficient_bound hqr
  have hc : 2 * (1 + q.choose (r + 1) *
      (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 20) := by
    calc
      _ ≤ (4 * q : ℝ) ^ 1 * (4 * q : ℝ) ^ (2 * q + 1) :=
        mul_le_mul (by simp only [pow_one]; linarith only [hq]) hK (by positivity)
          (by positivity)
      _ = (4 * q : ℝ) ^ (2 * q + 2) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := by
        have hh := paper_threshold_alpha_rpow_lower hqr hn (s := 2 * q + 2)
          (t := (1 / 20 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
        convert hh using 1
        congr 1
        ring
  have hh := mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg hn0.le (-(13 * paperAlpha q (r + 1) / 20)))
  have heq : (n : ℝ) ^ (paperAlpha q (r + 1) / 20) *
      (n : ℝ) ^ (-(13 * paperAlpha q (r + 1) / 20)) =
      (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  rw [heq] at hh
  nlinarith only [hh]

end Arxiv2411_18291
