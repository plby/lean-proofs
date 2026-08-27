import Arxiv.Arxiv2411_18291.LogNibbleEndConditions
import Arxiv.Arxiv2411_18291.FiniteSparseNibbleEnd

/-! # Logarithmic end conditions at the paper's original finite threshold -/

namespace Arxiv2411_18291

theorem sparse_log_nibble_end_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (hn : paperSizeThreshold q r ≤ n) {g : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g) :
    LogNibbleEndConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3 : ℝ))) g n
      (q - r + 1) := by
  let K := q.choose r
  let ρ := paperRho q r
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hρ : ρ ≤ 1 / 36 := paperRho_le_one_div_36 hqr
  refine ⟨?_, ?_⟩
  · have hnum := paper_threshold_nibble_monomial (C := 1056) (i := 0) (j := 3)
      (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 1056 * (K : ℝ) ^ 3 * r.factorial ≤ (n : ℝ) ^ ρ at hnum
    have hh := rpow_margin_of_density_lower (γ := (19 / 20 : ℝ)) (g := g) hn1
      (by positivity : (0 : ℝ) < 4 * r.factorial)
      (by simpa only [Real.rpow_natCast] using hg)
      (C := 264 * (K : ℝ) ^ 3) (α := ε / 3) (t := ρ) (u := 0)
      (by nlinarith only [hnum]) 3 (by norm_num; linarith only [hρ, hεhi])
    simpa only [Real.rpow_zero, mul_one] using hh
  · have hnum := paper_threshold_nibble_monomial (C := 4) (i := 1) (j := 0)
      (d := 0) hr hqr hn (by norm_num) (by norm_num) (by norm_num) (by omega)
    simp only [pow_zero, pow_one, Nat.factorial_zero, Nat.cast_one,
      Nat.cast_ofNat, mul_one] at hnum
    have hdq : ((q - r + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast (show q - r + 1 ≤ q by omega)
    have hh := rpow_margin_of_density_lower (γ := 1) (g := (n : ℝ)) hn1
      (by norm_num : (0 : ℝ) < 1) (by simp only [Real.rpow_one, div_one, le_refl])
      (C := 4 * ((q - r + 1 : ℕ) : ℝ)) (α := ε / 3) (t := ρ) (u := 0)
      (by nlinarith only [hnum, hdq]) 1 (by norm_num; linarith only [hρ, hεhi])
    simpa only [Real.rpow_zero, mul_one, pow_one] using hh

end Arxiv2411_18291
