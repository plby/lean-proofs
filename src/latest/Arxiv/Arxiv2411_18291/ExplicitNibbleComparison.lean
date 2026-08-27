import Arxiv.Arxiv2411_18291.ExplicitNibbleMargins

/-! # Finite nibble comparison parameters at the main theorem's scales -/

namespace Arxiv2411_18291

theorem nibble_comparison_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hk : 3 ≤ q.choose r) (hn : paperSizeThreshold q r ≤ n) {g D : ℝ}
    (hg : (n : ℝ) ^ r / (4 * r.factorial) ≤ g)
    (hD : (n : ℝ) ^ (q - r) / (4 * (q - r).factorial) ≤ D) :
    NibbleComparisonParameters (q.choose r) ((n : ℝ) ^ (-(1 / 9 : ℝ))) g D
      ((n : ℝ) ^ (-(1 / (9 * q.choose r) : ℝ))) ((n : ℝ) ^ (q - r - 1)) := by
  let K := q.choose r
  let ρ := paperRho q r
  let β : ℝ := 1 / (9 * K)
  have hkR : (3 : ℝ) ≤ K := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < K := by linarith only [hkR]
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hρ : ρ ≤ 1 / 36 := paperRho_le_one_div_36 hqr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hgap : ρ + 2 * β ≤ 1 / 9 := (paper_nibble_floor_gaps hqr hk).1
  have hhalf : 2 * (n : ℝ) ^ (-(1 / 9 : ℝ)) ≤ 1 := by
    simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat,
      mul_one, Real.rpow_zero] using
      paper_nibble_scaled_monomial (C := 2) (j := 0) (d := 0) hr hqr hn
        (by norm_num) (by norm_num) (by omega) (u := -(1 / 9)) (v := 0) (by linarith)
  have hsmall : (16 * (K : ℝ)) ^ 2 * (n : ℝ) ^ (-(1 / 9 : ℝ)) ≤ 1 := by
    have hh := paper_nibble_scaled_monomial (C := 256) (j := 2) (d := 0) hr hqr hn
      (by norm_num) (by norm_num) (by omega) (u := -(1 / 9)) (v := 0) (by linarith)
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one, Real.rpow_zero] at hh
    change 256 * (K : ℝ) ^ 2 * (n : ℝ) ^ (-(1 / 9 : ℝ)) ≤ 1 at hh
    nlinarith only [hh]
  have hden : 16 * (K : ℝ) ^ 3 * (n : ℝ) ^ (-(1 / 9 : ℝ)) ≤
      ((n : ℝ) ^ (-β)) ^ 2 := by
    rw [← Real.rpow_mul_natCast hn0.le]
    simpa only [Nat.factorial_zero, Nat.cast_one, mul_one, Nat.cast_ofNat] using
      paper_nibble_scaled_monomial (C := 16) (j := 3) (d := 0) hr hqr hn
        (by norm_num) (by norm_num) (by omega) (u := -(1 / 9)) (v := (-β) * 2)
        (by linarith only [hgap])
  have hmany : 16 * (K : ℝ) ^ 3 ≤ ((n : ℝ) ^ (-(1 / 9 : ℝ))) ^ 2 * g := by
    have hnum := paper_threshold_nibble_monomial (C := 64) (i := 0) (j := 3)
      (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 64 * (K : ℝ) ^ 3 * r.factorial ≤ (n : ℝ) ^ ρ at hnum
    have hh := rpow_margin_of_density_lower (γ := (r : ℝ)) (g := g) hn1
      (by positivity : (0 : ℝ) < 4 * r.factorial)
      (by simpa only [Real.rpow_natCast] using hg)
      (C := 16 * (K : ℝ) ^ 3) (α := 1 / 9) (t := ρ) (u := 0)
      (by nlinarith only [hnum]) 2 (by norm_num; linarith only [hρ, hrR])
    simpa only [Real.rpow_zero, mul_one] using hh
  have hcode : ((K : ℝ) ^ 2 + K) * (n : ℝ) ^ (q - r - 1) ≤
      ((n : ℝ) ^ (-(1 / 9 : ℝ))) ^ 2 * D := by
    have hnum := paper_threshold_nibble_monomial (C := 8) (i := 0) (j := 2)
      (d := q - r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) (Nat.sub_le _ _)
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 8 * (K : ℝ) ^ 2 * (q - r).factorial ≤ (n : ℝ) ^ ρ at hnum
    have hKK : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith only [hkR]
    have hKKmul := mul_le_mul_of_nonneg_right hKK
      (by positivity : (0 : ℝ) ≤ 4 * (q - r).factorial)
    have hsub : ((q - r - 1 : ℕ) : ℝ) = ((q - r : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ q - r by omega), Nat.cast_one]
    have hh := rpow_margin_of_density_lower (γ := ((q - r : ℕ) : ℝ)) (g := D) hn1
      (by positivity : (0 : ℝ) < 4 * (q - r).factorial)
      (by simpa only [Real.rpow_natCast] using hD)
      (C := (K : ℝ) ^ 2 + K) (α := 1 / 9) (t := ρ) (u := ((q - r - 1 : ℕ) : ℝ))
      (by nlinarith only [hnum, hKKmul]) 2 (by rw [hsub]; norm_num; linarith only [hρ])
    simpa only [Real.rpow_natCast] using hh
  have hpow : (n : ℝ) ^ (-(1 / 9 : ℝ)) ≤ ((n : ℝ) ^ (-β)) ^ K := by
    rw [← Real.rpow_mul_natCast hn0.le]
    apply le_of_eq
    congr 1
    dsimp only [β]
    field_simp
  refine ⟨hk, Real.rpow_pos_of_pos hn0 _, by linarith only [hhalf], ?_, ?_,
    Real.rpow_pos_of_pos hn0 _, ?_, hpow, hsmall, hden, hmany, by positivity, hcode⟩
  · exact (by positivity : (0 : ℝ) < (n : ℝ) ^ r / (4 * r.factorial)).trans_le hg
  · exact (by positivity : (0 : ℝ) < (n : ℝ) ^ (q - r) /
      (4 * (q - r).factorial)).trans_le hD
  · exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (by positivity))

end Arxiv2411_18291
