import Arxiv.Arxiv2411_18291.FocusingParameters
import Arxiv.Arxiv2411_18291.SmallPatternGreedyNumerics
import Arxiv.Arxiv2411_18291.AsymptoticPrescribedGreedy

/-! # Finite numerical conditions for focusing placements -/

namespace Arxiv2411_18291

theorem focusing_choose_bound {q r : ℕ} (hqr : r + 1 < q) :
    q.choose (r + 1) ≤ (4 * q) ^ (2 * q) :=
  (Nat.choose_le_two_pow q (r + 1)).trans
    ((Nat.pow_le_pow_left (by omega : 2 ≤ 4 * q) q).trans
      (Nat.pow_le_pow_right (by omega) (by omega : q ≤ 2 * q)))

theorem focusing_greedy_coefficient_bound {q r : ℕ} (hqr : r + 1 < q) :
    2 * (q.choose (r + 1) + 4 * (q.choose (r + 1)) ^ 2 * (r + 1).factorial) ≤
      (4 * q) ^ (5 * q + 2) := by
  have hc := small_pattern_greedy_coefficient_le (by omega : 2 ≤ q) hqr.le
    (focusing_choose_bound hqr)
  nlinarith only [hc]

theorem paper_focusing_smallness {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (q.choose (r + 1) : ℝ) * ((n : ℝ) ^ (-paperRho q (r + 1)) +
      q.choose (r + 1) * (4 * (r + 1).factorial * (n : ℝ) ^ (-paperRho q (r + 1)) /
        (n : ℝ) ^ (-paperFocusingExponent q (r + 1)))) ≤
      (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) / 2 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  obtain ⟨_, hgap2, hgap, _⟩ := paper_focusing_parameters hqr
  have hc : (2 * (q.choose (r + 1) +
      4 * (q.choose (r + 1)) ^ 2 * (r + 1).factorial) : ℝ) ≤
      (n : ℝ) ^ paperAlpha q (r + 1) := by
    have hg := paper_threshold_alpha_rpow_lower hqr hn (s := 5 * q + 2)
      (t := 1) (by norm_num) (by push_cast; linarith only [hq])
    simp only [mul_one] at hg
    have hcast : (2 * (q.choose (r + 1) +
        4 * (q.choose (r + 1)) ^ 2 * (r + 1).factorial) : ℝ) ≤
        (4 * q : ℝ) ^ (5 * q + 2) := by
      exact_mod_cast focusing_greedy_coefficient_bound hqr
    exact hcast.trans hg
  have hh := mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg hn0.le (-paperAlpha q (r + 1)))
  rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hh
  have hscaled : (q.choose (r + 1) : ℝ) *
      ((n : ℝ) ^ (-(paperRho q (r + 1) - paperFocusingExponent q (r + 1))) +
        q.choose (r + 1) * (4 * (r + 1).factorial *
          (n : ℝ) ^ (-(paperRho q (r + 1) - 2 * paperFocusingExponent q (r + 1))))) ≤
      1 / 2 := by
    calc
      _ ≤ (q.choose (r + 1) : ℝ) * ((n : ℝ) ^ (-paperAlpha q (r + 1)) +
          q.choose (r + 1) * (4 * (r + 1).factorial *
            (n : ℝ) ^ (-paperAlpha q (r + 1)))) := by
        gcongr
      _ ≤ _ := by nlinarith only [hh]
  have hdiv : ((q.choose (r + 1) : ℝ) * ((n : ℝ) ^ (-paperRho q (r + 1)) +
      q.choose (r + 1) * (4 * (r + 1).factorial * (n : ℝ) ^ (-paperRho q (r + 1)) /
        (n : ℝ) ^ (-paperFocusingExponent q (r + 1))))) /
      (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) ≤ 1 / 2 := by
    rw [prescribed_smallness_scale hn0]
    exact hscaled
  have hm := (div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)).mp hdiv
  linarith only [hm]

theorem paper_focusing_failure_lt_one {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (q.choose (r + 1) : ℝ) * n.choose r * Real.exp
      (-((2 * (r + 1).factorial * (n : ℝ) ^ (-paperRho q (r + 1)) * n /
        (n : ℝ) ^ (-paperFocusingExponent q (r + 1))) / 3)) < 1 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hK : q.choose (r + 1) ≤ n := (focusing_choose_bound hqr).trans
    ((Nat.pow_le_pow_right (by omega) (by omega : 2 * q ≤ 90 * q)).trans
      ((boost_threshold_le_paper_threshold hqr).trans hn))
  have htail := absorber_greedy_failure_lt_one hqr hn hK
    (Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg (paper_focusing_parameters hqr).2.2.2))
  have heq : 2 * ((r + 1).factorial : ℝ) * (n : ℝ) ^ (-paperRho q (r + 1)) * n /
      (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) =
      2 * (r + 1).factorial *
        (n : ℝ) ^ (-(paperRho q (r + 1) - paperFocusingExponent q (r + 1))) * n := by
    calc
      _ = 2 * ((r + 1).factorial : ℝ) *
          ((n : ℝ) ^ (-paperRho q (r + 1)) /
            (n : ℝ) ^ (-paperFocusingExponent q (r + 1))) * n := by ring
      _ = _ := by rw [rpow_density_ratio hn0]
  rw [heq]
  exact htail

theorem focusing_degree_bound_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (n : ℝ) ^ (-paperRho q (r + 1)) + q.choose (r + 1) *
      (4 * (r + 1).factorial *
        (n : ℝ) ^ (-(paperRho q (r + 1) - paperFocusingExponent q (r + 1)))) ≤
      (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hk : 1 ≤ q.choose (r + 1) := Nat.choose_pos hqr.le
  have hk2 : q.choose (r + 1) ≤ (q.choose (r + 1)) ^ 2 := Nat.le_self_pow two_ne_zero _
  have hkm := Nat.mul_le_mul_right (4 * (r + 1).factorial) hk2
  have hcNat : 1 + 4 * q.choose (r + 1) * (r + 1).factorial ≤
      (4 * q) ^ (5 * q + 2) := by
    have hh := focusing_greedy_coefficient_bound hqr
    nlinarith only [hk, hkm, hh]
  have hc : (1 + 4 * q.choose (r + 1) * (r + 1).factorial : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) * (3 / 10)) := by
    have hcast : (1 + 4 * q.choose (r + 1) * (r + 1).factorial : ℝ) ≤
        (4 * q : ℝ) ^ (5 * q + 2) := by exact_mod_cast hcNat
    exact hcast.trans
      (paper_threshold_alpha_rpow_lower hqr hn (s := 5 * q + 2)
        (t := (3 / 10 : ℝ)) (by norm_num) (by push_cast; linarith only [hq]))
  calc
    _ ≤ (n : ℝ) ^ (-paperAlpha q (r + 1)) + q.choose (r + 1) *
        (4 * (r + 1).factorial * (n : ℝ) ^ (-paperAlpha q (r + 1))) := by
      gcongr
      · exact paperAlpha_le_rho hqr
      · exact (paper_focusing_parameters hqr).2.2.1
    _ = (1 + 4 * q.choose (r + 1) * (r + 1).factorial : ℝ) *
        (n : ℝ) ^ (-paperAlpha q (r + 1)) := by ring
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) * (3 / 10)) *
        (n : ℝ) ^ (-paperAlpha q (r + 1)) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

end Arxiv2411_18291
