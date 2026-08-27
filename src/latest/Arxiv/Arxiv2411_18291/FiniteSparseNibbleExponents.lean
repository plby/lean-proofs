import Arxiv.Arxiv2411_18291.FiniteSparseNibbleEnd
import Arxiv.Arxiv2411_18291.ExplicitNibbleFaceMargin

/-! # Finite concentration margins at polynomially sparse nibble densities -/

namespace Arxiv2411_18291

theorem sparse_nibble_exponents_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    {ε : ℝ} (hεhi : ε ≤ 2 / 5) (hn : paperSizeThreshold q r ≤ n) {g D : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g)
    (hD : (n : ℝ) ^ (((q - r : ℕ) : ℝ) - 1 / 3) / (4 * (q - r).factorial) ≤ D) :
    NibbleExponentConditions (q.choose r) (q - r + 1)
      ((n : ℝ) ^ (-(ε / 3 : ℝ))) g D n ((n : ℝ) ^ (q - r - 1))
      ((n : ℝ) ^ (1 / 10 : ℝ)) ((n : ℝ) ^ (-(1 / 20 : ℝ)) / (4 * r.factorial)) := by
  let K := q.choose r
  let ρ := paperRho q r
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hρ : ρ ≤ 1 / 36 := paperRho_le_one_div_36 hqr
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · have hnum := paper_threshold_nibble_monomial (C := 1115136) (i := 0) (j := 6)
      (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 1115136 * (K : ℝ) ^ 6 * r.factorial ≤ (n : ℝ) ^ ρ at hnum
    exact rpow_margin_of_density_lower (γ := (19 / 20 : ℝ)) (g := g) hn1
      (by positivity : (0 : ℝ) < 4 * r.factorial)
      (by simpa only [Real.rpow_natCast] using hg)
      (C := 16 * (132 * (K : ℝ) ^ 3) ^ 2) (α := ε / 3) (t := ρ) (u := 1 / 10)
      (by nlinarith only [hnum]) 6 (by norm_num; linarith only [hρ, hεhi])
  · have hnum := paper_threshold_nibble_monomial (C := 704) (i := 0) (j := 3)
      (d := q - r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) (Nat.sub_le _ _)
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 704 * (K : ℝ) ^ 3 * (q - r).factorial ≤ (n : ℝ) ^ ρ at hnum
    have hsub : ((q - r - 1 : ℕ) : ℝ) = ((q - r : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ q - r by omega), Nat.cast_one]
    have hh := rpow_margin_of_density_lower (γ := ((q - r : ℕ) : ℝ) - 1 / 3) (g := D) hn1
      (by positivity : (0 : ℝ) < 4 * (q - r).factorial)
      (by simpa only [Real.rpow_natCast] using hD)
      (C := 176 * (K : ℝ) ^ 3) (α := ε / 3) (t := ρ)
      (u := 1 / 10 + ((q - r - 1 : ℕ) : ℝ))
      (by nlinarith only [hnum]) 4 (by rw [hsub]; norm_num; linarith only [hρ, hεhi])
    simpa only [Real.rpow_add hn0, Real.rpow_natCast, mul_assoc] using hh
  · have hnum := paper_threshold_nibble_monomial (C := 1408) (i := 0) (j := 4)
      (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 1408 * (K : ℝ) ^ 4 * r.factorial ≤ (n : ℝ) ^ ρ at hnum
    exact rpow_margin_of_density_lower (γ := (19 / 20 : ℝ)) (g := g) hn1
      (by positivity : (0 : ℝ) < 4 * r.factorial)
      (by simpa only [Real.rpow_natCast] using hg)
      (C := 352 * (K : ℝ) ^ 4) (α := ε / 3) (t := ρ) (u := 1 / 10)
      (by nlinarith only [hnum]) 4 (by norm_num; linarith only [hρ, hεhi])
  · let d := q - r + 1
    let f : ℝ := 4 * r.factorial
    let X : ℝ := (n : ℝ) ^ (1 / 20 : ℝ)
    have hX : 1 ≤ X := Real.one_le_rpow hn1 (by norm_num)
    have hnum := paper_nibble_face_constant hr hqr hn
    dsimp only at hnum
    have heq : (K : ℝ) / ((n : ℝ) ^ (-(1 / 20 : ℝ)) / f) = K * f * X := by
      rw [div_div_eq_mul_div, Real.rpow_neg hn0.le, div_inv_eq_mul]
    have hcoef : 8 * (4 * (d : ℝ) * (1 + 128 * K) * K +
        ((d : ℝ) + K / ((n : ℝ) ^ (-(1 / 20 : ℝ)) / f))) ≤
          (n : ℝ) ^ ρ * X := by
      rw [heq]
      have hbase : 0 ≤ 8 * (4 * (d : ℝ) * (1 + 128 * K) * K + d) := by positivity
      have hm := mul_le_mul_of_nonneg_left hX hbase
      have hb : 8 * (4 * (d : ℝ) * (1 + 128 * K) * K + (d + K * f)) ≤
          (n : ℝ) ^ ρ := by
        simpa only [d, K, f, div_div_eq_mul_div, div_one] using hnum
      have hbx := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ X)
      nlinarith only [hm, hbx]
    have hscaled := mul_le_mul_of_nonneg_right hcoef
      (Real.rpow_nonneg hn0.le (1 / 10 : ℝ))
    have hmargin : ((n : ℝ) ^ ρ * X) * (n : ℝ) ^ (1 / 10 : ℝ) ≤
        ((n : ℝ) ^ (-(ε / 3))) ^ 2 * n := by
      dsimp only [X]
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0,
        ← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add_one hn0.ne']
      apply Real.rpow_le_rpow_of_exponent_le hn1
      norm_num
      linarith only [hρ, hεhi]
    exact hscaled.trans hmargin
  · have heq : ((n : ℝ) ^ (-(1 / 20 : ℝ)) / (4 * r.factorial)) * n =
        (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add_one hn0.ne']
      norm_num
    rw [heq]
    exact hg

end Arxiv2411_18291
