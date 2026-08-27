import Arxiv.Arxiv2411_18291.SharpWeightedDecoderCoefficient

/-! # Constant-deviation decoder concentration from the small edge cap -/

namespace Arxiv2411_18291

theorem capped_weighted_decoder_exponent_lower {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (2 / 3 : ℝ) * (n : ℝ) ^ (paperAlpha q (r + 1) / 10) ≤
      4 * (r + 1).factorial * (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) * n /
        (3 * (1 + (n : ℝ) ^ (paperAlpha q (r + 1) / 10))) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hα := paperAlpha_pos hqr
  have hαmax := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  let x : ℝ := (n : ℝ) ^ (paperAlpha q (r + 1) / 10)
  let θ : ℝ := (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))
  have hx : 1 ≤ x := Real.one_le_rpow hn1 (by positivity)
  have hθn : x * x ≤ θ * n := by
    calc
      _ = (n : ℝ) ^ (paperAlpha q (r + 1) / 5) := by
        dsimp only [x]
        rw [← Real.rpow_add hn0]
        congr 1
        ring
      _ ≤ (n : ℝ) ^ (1 - 3 * paperAlpha q (r + 1) / 5) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hαmax])
      _ = _ := by
        dsimp only [θ]
        rw [← Real.rpow_add_one hn0.ne']
        congr 1
        ring
  have hf : (1 : ℝ) ≤ (r + 1).factorial := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hfac := mul_le_mul_of_nonneg_right hf (show 0 ≤ θ * n by dsimp only [θ]; positivity)
  change (2 / 3 : ℝ) * x ≤ 4 * (r + 1).factorial * θ * n / (3 * (1 + x))
  apply (le_div_iff₀ (show (0 : ℝ) < 3 * (1 + x) by positivity)).mpr
  nlinarith only [hx, hθn, hfac]

theorem capped_weighted_decoder_finite_conditions {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let θ := (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))
    let K := (q + (r + 1)).choose (r + 1)
    0 < n ∧ 4 * (q + (r + 1)) ^ 2 ≤ n ∧
      (K : ℝ) * (θ + K * (8 * (r + 1).factorial * θ)) ≤ 1 / 4 ∧
      (K : ℝ) * n.choose r * Real.exp (-(4 * (r + 1).factorial * θ * n /
        (3 * (1 + (n : ℝ) ^ (paperAlpha q (r + 1) / 10))))) < 1 := by
  dsimp only
  obtain ⟨hn0, hsize, hsmall, _⟩ := weighted_decoder_finite_conditions hqr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn0
  have hα := paperAlpha_pos hqr
  have hx : 1 ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) :=
    Real.one_le_rpow hn1 (by positivity)
  have hL : 8 * (r + 1).factorial * (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) ≤
      (1 + (n : ℝ) ^ (paperAlpha q (r + 1) / 10)) *
        (2 * (r + 1).factorial * ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) +
          (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)))) := by
    have hh := mul_le_mul_of_nonneg_right
      (show (2 : ℝ) ≤ 1 + (n : ℝ) ^ (paperAlpha q (r + 1) / 10) by linarith only [hx])
      (show 0 ≤ 2 * (r + 1).factorial *
        ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) +
          (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))) by positivity)
    nlinarith only [hh]
  refine ⟨hn0, hsize, ?_, ?_⟩
  · apply le_trans _ hsmall
    gcongr
  · have hK : (q + (r + 1)).choose (r + 1) ≤ (4 * q) ^ (2 * q) :=
      (small_clique_pattern_bounds_sharp (by omega : 2 ≤ q)
        (by omega : q + (r + 1) ≤ 2 * q)).2
    have hKn : (q + (r + 1)).choose (r + 1) ≤ n := hK.trans
      ((Nat.pow_le_pow_right (by omega) (by omega : 2 * q ≤ 90 * q)).trans
        ((boost_threshold_le_paper_threshold hqr).trans hn))
    apply lt_of_le_of_lt _ (weighted_decoder_polynomial_tail hqr hn hKn)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (neg_le_neg (capped_weighted_decoder_exponent_lower hqr hn))

theorem capped_weighted_decoder_output_density {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let θ := (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))
    let K := (q + (r + 1)).choose (r + 1)
    θ + K * (8 * (r + 1).factorial * θ) ≤
        (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30)) ∧
      (2 ^ q * (r + 1).factorial : ℕ) *
        (θ + (q + 1).choose (q - r) * (K * (8 * (r + 1).factorial * θ))) ≤
          (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30)) := by
  dsimp only
  have hprod := weightedDecoderCoefficient_density_paper_threshold hqr hn
  constructor
  · apply le_trans _ hprod
    have hc : (1 + (q + (r + 1)).choose (r + 1) * (8 * (r + 1).factorial) : ℝ) ≤
        weightedDecoderCoefficient q r := by
      exact_mod_cast weightedDecoderCoefficient_graph_le q r
    calc
      _ = (1 + (q + (r + 1)).choose (r + 1) * (8 * (r + 1).factorial)) *
          (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  · apply le_trans _ hprod
    have heq : (2 ^ q * (r + 1).factorial : ℕ) *
        ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) + (q + 1).choose (q - r) *
          ((q + (r + 1)).choose (r + 1) *
            (8 * (r + 1).factorial * (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))))) =
        (weightedDecoderCoefficient q r : ℝ) *
          (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) := by
      simp only [weightedDecoderCoefficient, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
      ring
    exact heq.le

end Arxiv2411_18291
