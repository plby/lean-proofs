import Arxiv.Arxiv2411_18291.CappedFirstElimination

/-! # The further cancellation constants fit the original threshold -/

noncomputable section

namespace Arxiv2411_18291

def furtherVariableCoefficient (q r H : ℕ) : ℕ :=
  4 * q.choose (r + 1) + 2 * (q - r) + 2 * (1 + H * (4 * (r + 1).factorial))

theorem first_le_furtherVariableCoefficient (q r H : ℕ) :
    1 + H * (4 * (r + 1).factorial) ≤ furtherVariableCoefficient q r H := by
  unfold furtherVariableCoefficient
  omega

theorem one_le_furtherVariableCoefficient (q r H : ℕ) :
    1 ≤ furtherVariableCoefficient q r H :=
  (by omega : 1 ≤ 1 + H * (4 * (r + 1).factorial)).trans
    (first_le_furtherVariableCoefficient q r H)

theorem further_variable_elimination_coefficient {q r H : ℕ} (hqr : r + 1 < q)
    (hH : H ≤ (4 * q) ^ (2 * q)) :
    furtherVariableCoefficient q r H ≤ (4 * q) ^ (5 * q) := by
  have hq : 2 ≤ q := by omega
  have hk : q.choose (r + 1) ≤ (4 * q) ^ (4 * q) :=
    (Nat.choose_le_two_pow _ _).trans ((Nat.pow_le_pow_left (by omega) q).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have hd : q - r ≤ (4 * q) ^ (4 * q) := by
    calc
      _ ≤ 4 * q := by omega
      _ = (4 * q) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hc := first_variable_elimination_coefficient hqr hH
  calc
    _ ≤ 8 * (4 * q) ^ (4 * q) := by unfold furtherVariableCoefficient; omega
    _ ≤ (4 * q) * (4 * q) ^ (4 * q) := Nat.mul_le_mul_right _ (by omega)
    _ = (4 * q) ^ (4 * q + 1) := (pow_succ' _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem capped_further_input_interval {q r n H : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hH : H ≤ (4 * q) ^ (2 * q)) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ furtherVariableCoefficient q r H *
      (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)) ∧
    furtherVariableCoefficient q r H * (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)) ≤
      (4 * q : ℝ) ^ (24 * q) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hα := paperAlpha_pos hqr
  have hαmax := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hc : (1 : ℝ) ≤ furtherVariableCoefficient q r H := by
    exact_mod_cast one_le_furtherVariableCoefficient q r H
  constructor
  · exact (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hαmax])).trans
      (le_mul_of_one_le_left (by positivity) hc)
  · have hC : (furtherVariableCoefficient q r H : ℝ) ≤ (4 * q : ℝ) ^ (24 * q) := by
      exact_mod_cast (further_variable_elimination_coefficient hqr hH).trans
        (Nat.pow_le_pow_right (by omega) (by omega : 5 * q ≤ 24 * q))
    exact mul_le_mul hC
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hα]))
      (by positivity) (by positivity)

theorem capped_further_output_density {q r n H : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hH : H ≤ (4 * q) ^ (2 * q)) :
    let θ : ℝ := furtherVariableCoefficient q r H *
      (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45))
    θ + H * (4 * (r + 1).factorial * θ) ≤
      (n : ℝ) ^ (-(5 * paperAlpha q (r + 1) / 18)) := by
  dsimp only
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hc : (1 + H * (4 * (r + 1).factorial) : ℝ) * furtherVariableCoefficient q r H ≤
      (4 * q : ℝ) ^ (9 * q) := by
    have hh := Nat.mul_le_mul (first_variable_elimination_coefficient hqr hH)
      (further_variable_elimination_coefficient hqr hH)
    rw [← pow_add, show 4 * q + 5 * q = 9 * q by omega] at hh
    exact_mod_cast hh
  have hg : (4 * q : ℝ) ^ (9 * q) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
    have hh := paper_threshold_alpha_rpow_lower hqr hn (s := 9 * q)
      (t := (1 / 10 : ℝ)) (by norm_num) (by push_cast; linarith)
    convert hh using 1
    congr 1
    ring
  calc
    _ = ((1 + H * (4 * (r + 1).factorial)) * furtherVariableCoefficient q r H) *
        (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)) := by ring
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) *
        (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)) :=
      mul_le_mul_of_nonneg_right (hc.trans hg) (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

end Arxiv2411_18291
