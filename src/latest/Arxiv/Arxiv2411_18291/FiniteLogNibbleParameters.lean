import Arxiv.Arxiv2411_18291.FiniteLogNibbleEnd

/-! # All logarithmic tracking parameters at the original paper threshold -/

namespace Arxiv2411_18291

theorem sparse_log_nibble_parameters_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hk : 3 ≤ q.choose r) (hk5 : q.choose r ≤ 5) {ε : ℝ}
    (hεhi : ε ≤ 2 / 5) {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1)
    (hpow : (n : ℝ) ^ (-(ε / 3)) ≤ ((2 / 5 : ℝ) * p₀) ^ (q.choose r))
    (hn : paperSizeThreshold q r ≤ n) {g D : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g)
    (hD : (n : ℝ) ^ (((q - r : ℕ) : ℝ) - 1 / 3) / (4 * (q - r).factorial) ≤ D) :
    LogNibbleParameters (q.choose r) ((n : ℝ) ^ (-(ε / 3 : ℝ))) g D
      p₀ ((n : ℝ) ^ (q - r - 1)) := by
  let K := q.choose r
  let ρ := paperRho q r
  have hkR : (3 : ℝ) ≤ K := by exact_mod_cast hk
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hρ : ρ ≤ 1 / 36 := paperRho_le_one_div_36 hqr
  have hmany : 200 * (K : ℝ) ^ 3 ≤ ((n : ℝ) ^ (-(ε / 3 : ℝ))) ^ 2 * g := by
    have hnum := paper_threshold_nibble_monomial (C := 800) (i := 0) (j := 3)
      (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 800 * (K : ℝ) ^ 3 * r.factorial ≤ (n : ℝ) ^ ρ at hnum
    have hh := rpow_margin_of_density_lower (γ := (19 / 20 : ℝ)) (g := g) hn1
      (by positivity : (0 : ℝ) < 4 * r.factorial)
      (by simpa only [Real.rpow_natCast] using hg)
      (C := 200 * (K : ℝ) ^ 3) (α := ε / 3) (t := ρ) (u := 0)
      (by nlinarith only [hnum]) 2 (by norm_num; linarith only [hρ, hεhi])
    simpa only [Real.rpow_zero, mul_one] using hh
  have hcode : ((K : ℝ) ^ 2 + K) * (n : ℝ) ^ (q - r - 1) ≤
      ((n : ℝ) ^ (-(ε / 3 : ℝ))) ^ 2 * D / 100 := by
    have hnum := paper_threshold_nibble_monomial (C := 800) (i := 0) (j := 2)
      (d := q - r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) (Nat.sub_le _ _)
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 800 * (K : ℝ) ^ 2 * (q - r).factorial ≤ (n : ℝ) ^ ρ at hnum
    have hKK : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith only [hkR]
    have hKKmul := mul_le_mul_of_nonneg_right hKK
      (by positivity : (0 : ℝ) ≤ 400 * (q - r).factorial)
    have hsub : ((q - r - 1 : ℕ) : ℝ) = ((q - r : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ q - r by omega), Nat.cast_one]
    have hh := rpow_margin_of_density_lower (γ := ((q - r : ℕ) : ℝ) - 1 / 3) (g := D) hn1
      (by positivity : (0 : ℝ) < 4 * (q - r).factorial)
      (by simpa only [Real.rpow_natCast] using hD)
      (C := 100 * ((K : ℝ) ^ 2 + K)) (α := ε / 3) (t := ρ)
      (u := ((q - r - 1 : ℕ) : ℝ))
      (by nlinarith only [hnum, hKKmul]) 2 (by rw [hsub]; norm_num; linarith only [hρ, hεhi])
    simp only [Real.rpow_natCast] at hh
    nlinarith only [hh]
  have hcount : (K : ℝ) ≤ ((n : ℝ) ^ (-(ε / 3 : ℝ))) ^ 3 * g := by
    have hR := sparse_log_nibble_end_paper_threshold hr hqr hεhi hn hg
    have hlarge := hR.count_many_edges
    have hk2 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith only [hkR]
    have hk3 := mul_le_mul_of_nonneg_right hk2 (Nat.cast_nonneg K (α := ℝ))
    have hk3n : (0 : ℝ) ≤ (K : ℝ) ^ 3 := by positivity
    nlinarith only [hlarge, hk3, hk3n]
  have hoverlap : (n : ℝ) ^ (q - r - 1) ≤ ((n : ℝ) ^ (-(ε / 3 : ℝ))) ^ 3 * D := by
    have hnum := paper_threshold_nibble_monomial (C := 4) (i := 0) (j := 0)
      (d := q - r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) (Nat.sub_le _ _)
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    have hsub : ((q - r - 1 : ℕ) : ℝ) = ((q - r : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ q - r by omega), Nat.cast_one]
    have hh := rpow_margin_of_density_lower (γ := ((q - r : ℕ) : ℝ) - 1 / 3) (g := D) hn1
      (by positivity : (0 : ℝ) < 4 * (q - r).factorial)
      (by simpa only [Real.rpow_natCast] using hD)
      (C := 1) (α := ε / 3) (t := ρ) (u := ((q - r - 1 : ℕ) : ℝ))
      (by simpa only [one_mul] using hnum) 3 (by rw [hsub]; norm_num; linarith only [hρ, hεhi])
    simpa only [Real.rpow_natCast, one_mul] using hh
  refine ⟨hk, hk5, Real.rpow_pos_of_pos hn0 _, ?_, ?_, hp₀, hp₁, hpow,
    hmany, hcount, by positivity, hcode, hoverlap⟩
  · exact (by positivity : (0 : ℝ) < (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial)).trans_le hg
  · exact (by positivity : (0 : ℝ) < (n : ℝ) ^ (((q - r : ℕ) : ℝ) - 1 / 3) /
      (4 * (q - r).factorial)).trans_le hD

end Arxiv2411_18291
