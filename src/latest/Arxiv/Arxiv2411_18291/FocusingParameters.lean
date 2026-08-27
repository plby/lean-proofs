import Arxiv.Arxiv2411_18291.PaperParameterMargins
import Arxiv.Arxiv2411_18291.PaperAlphaGrowth

/-! # Finite focusing parameters and their exponent margins -/

noncomputable section

namespace Arxiv2411_18291

def paperFocusingExponent (q r : ℕ) : ℝ :=
  paperAlpha q r * ((q.choose r - 1 : ℕ) : ℝ) + paperAlpha q r / 2

theorem paper_focusing_parameters {q r : ℕ} (hqr : r + 1 < q) :
    0 ≤ paperFocusingExponent q (r + 1) ∧
      paperAlpha q (r + 1) ≤ paperRho q (r + 1) - 2 * paperFocusingExponent q (r + 1) ∧
      paperAlpha q (r + 1) ≤ paperRho q (r + 1) - paperFocusingExponent q (r + 1) ∧
      paperRho q (r + 1) - paperFocusingExponent q (r + 1) ≤ 1 / 2 := by
  have hα := paperAlpha_pos hqr
  have hk : 1 ≤ q.choose (r + 1) := Nat.choose_pos hqr.le
  have hKα : (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1) ≤
      paperRho q (r + 1) / 2 := by
    by_cases hr : r = 0
    · subst r
      exact (paperAlpha_mul_choose_rankOne (by omega : 1 < q)).le
    · exact (paperAlpha_mul_choose_lt_half_rho (by omega : 2 ≤ r + 1) hqr).le
  have heq : paperFocusingExponent q (r + 1) =
      paperAlpha q (r + 1) * q.choose (r + 1) - paperAlpha q (r + 1) / 2 := by
    unfold paperFocusingExponent
    rw [Nat.cast_sub hk, Nat.cast_one]
    ring
  have ha : 0 ≤ paperFocusingExponent q (r + 1) := by
    unfold paperFocusingExponent
    positivity
  have hgap : paperAlpha q (r + 1) ≤
      paperRho q (r + 1) - 2 * paperFocusingExponent q (r + 1) := by
    rw [heq]
    nlinarith only [hKα]
  have hρ := paperRho_le_one_div_36 hqr
  exact ⟨ha, hgap, by linarith only [ha, hgap], by linarith only [ha, hρ]⟩

theorem paper_factorial_margin_half_alpha {q r n d : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hd : d ≤ q) :
    (8 * d.factorial : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 2) := by
  have hc : 8 * d.factorial ≤ (4 * q) ^ (q + 1) := by
    calc
      _ ≤ (4 * q) ^ 1 * (4 * q) ^ q := Nat.mul_le_mul
        (by simp only [pow_one]; omega)
        ((Nat.factorial_le hd).trans ((Nat.factorial_le_pow q).trans
          (Nat.pow_le_pow_left (by omega) q)))
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hg : (4 * q : ℝ) ^ (q + 1) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 2) := by
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hh := paper_threshold_alpha_rpow_lower hqr hn (s := q + 1)
      (t := (1 / 2 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
    convert hh using 1
    congr 1
    ring
  exact (by exact_mod_cast hc : (8 * d.factorial : ℝ) ≤ (4 * q : ℝ) ^ (q + 1)).trans hg

end Arxiv2411_18291
