import Arxiv.Arxiv2411_18291.ExplicitNibbleEnd
import Arxiv.Arxiv2411_18291.ExplicitNibbleFaceMargin

/-! # Explicit common concentration exponent for the nibble -/

namespace Arxiv2411_18291

theorem nibble_exponents_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : paperSizeThreshold q r ≤ n) {g D : ℝ}
    (hg : (n : ℝ) ^ r / (4 * r.factorial) ≤ g)
    (hD : (n : ℝ) ^ (q - r) / (4 * (q - r).factorial) ≤ D) :
    NibbleExponentConditions (q.choose r) (q - r + 1)
      ((n : ℝ) ^ (-(1 / 9 : ℝ))) g D n ((n : ℝ) ^ (q - r - 1))
      ((n : ℝ) ^ (1 / 6 : ℝ)) (1 / (4 * r.factorial)) := by
  let K := q.choose r
  let ρ := paperRho q r
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hρ : ρ ≤ 1 / 36 := paperRho_le_one_div_36 hqr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · have hnum := paper_threshold_nibble_monomial (C := 1115136) (i := 0) (j := 6)
      (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 1115136 * (K : ℝ) ^ 6 * r.factorial ≤ (n : ℝ) ^ ρ at hnum
    exact rpow_margin_of_density_lower (γ := (r : ℝ)) (g := g) hn1
      (by positivity : (0 : ℝ) < 4 * r.factorial)
      (by simpa only [Real.rpow_natCast] using hg)
      (C := 16 * (132 * (K : ℝ) ^ 3) ^ 2) (α := 1 / 9) (t := ρ) (u := 1 / 6)
      (by nlinarith only [hnum]) 6 (by norm_num; linarith only [hρ, hrR])
  · have hnum := paper_threshold_nibble_monomial (C := 704) (i := 0) (j := 3)
      (d := q - r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) (Nat.sub_le _ _)
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 704 * (K : ℝ) ^ 3 * (q - r).factorial ≤ (n : ℝ) ^ ρ at hnum
    have hsub : ((q - r - 1 : ℕ) : ℝ) = ((q - r : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ q - r by omega), Nat.cast_one]
    have hh := rpow_margin_of_density_lower (γ := ((q - r : ℕ) : ℝ)) (g := D) hn1
      (by positivity : (0 : ℝ) < 4 * (q - r).factorial)
      (by simpa only [Real.rpow_natCast] using hD)
      (C := 176 * (K : ℝ) ^ 3) (α := 1 / 9) (t := ρ)
      (u := 1 / 6 + ((q - r - 1 : ℕ) : ℝ))
      (by nlinarith only [hnum]) 4 (by rw [hsub]; norm_num; linarith only [hρ])
    simpa only [Real.rpow_add hn0, Real.rpow_natCast, mul_assoc] using hh
  · have hnum := paper_threshold_nibble_monomial (C := 1408) (i := 0) (j := 4)
      (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 1408 * (K : ℝ) ^ 4 * r.factorial ≤ (n : ℝ) ^ ρ at hnum
    exact rpow_margin_of_density_lower (γ := (r : ℝ)) (g := g) hn1
      (by positivity : (0 : ℝ) < 4 * r.factorial)
      (by simpa only [Real.rpow_natCast] using hg)
      (C := 352 * (K : ℝ) ^ 4) (α := 1 / 9) (t := ρ) (u := 1 / 6)
      (by nlinarith only [hnum]) 4 (by norm_num; linarith only [hρ, hrR])
  · have hnum := paper_nibble_face_constant hr hqr hn
    dsimp only at hnum
    exact rpow_margin_of_density_lower (γ := 1) (g := (n : ℝ)) hn1
      (by norm_num : (0 : ℝ) < 1) (by simp only [Real.rpow_one, div_one, le_refl])
      (α := 1 / 9) (t := ρ) (u := 1 / 6)
      (by simpa only [mul_one] using hnum) 2 (by norm_num; linarith only [hρ])
  · have hpow : (n : ℝ) ≤ (n : ℝ) ^ r := by
      simpa only [Real.rpow_one, Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le hn1 hrR
    have hh := (div_le_div_of_nonneg_right hpow
      (by positivity : (0 : ℝ) ≤ 4 * r.factorial)).trans hg
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hh

end Arxiv2411_18291
