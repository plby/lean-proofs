import Arxiv.Arxiv2411_18291.FiniteNibbleFloors

/-! # Finite comparison parameters for the sparse, variable-error nibble -/

namespace Arxiv2411_18291

theorem sparse_nibble_comparison_at_floor_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hk : 3 ≤ q.choose r) {ε : ℝ}
    (hεhi : ε ≤ 2 / 5) {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1)
    (hpow : (n : ℝ) ^ (-(ε / 3)) ≤ p₀ ^ (q.choose r))
    (hF : NibbleFloorConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
      p₀)
    (hn : paperSizeThreshold q r ≤ n) {g D : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g)
    (hD : (n : ℝ) ^ (((q - r : ℕ) : ℝ) - 1 / 3) / (4 * (q - r).factorial) ≤ D) :
    NibbleComparisonParameters (q.choose r) ((n : ℝ) ^ (-(ε / 3 : ℝ))) g D
      p₀ ((n : ℝ) ^ (q - r - 1)) := by
  let K := q.choose r
  let ρ := paperRho q r
  have hkR : (3 : ℝ) ≤ K := by exact_mod_cast hk
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hρ : ρ ≤ 1 / 36 := paperRho_le_one_div_36 hqr
  have hmany : 16 * (K : ℝ) ^ 3 ≤ ((n : ℝ) ^ (-(ε / 3 : ℝ))) ^ 2 * g := by
    have hnum := paper_threshold_nibble_monomial (C := 64) (i := 0) (j := 3)
      (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 64 * (K : ℝ) ^ 3 * r.factorial ≤ (n : ℝ) ^ ρ at hnum
    have hh := rpow_margin_of_density_lower (γ := (19 / 20 : ℝ)) (g := g) hn1
      (by positivity : (0 : ℝ) < 4 * r.factorial)
      (by simpa only [Real.rpow_natCast] using hg)
      (C := 16 * (K : ℝ) ^ 3) (α := ε / 3) (t := ρ) (u := 0)
      (by nlinarith only [hnum]) 2 (by norm_num; linarith only [hρ, hεhi])
    simpa only [Real.rpow_zero, mul_one] using hh
  have hcode : ((K : ℝ) ^ 2 + K) * (n : ℝ) ^ (q - r - 1) ≤
      ((n : ℝ) ^ (-(ε / 3 : ℝ))) ^ 2 * D := by
    have hnum := paper_threshold_nibble_monomial (C := 8) (i := 0) (j := 2)
      (d := q - r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) (Nat.sub_le _ _)
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 8 * (K : ℝ) ^ 2 * (q - r).factorial ≤ (n : ℝ) ^ ρ at hnum
    have hKK : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith only [hkR]
    have hKKmul := mul_le_mul_of_nonneg_right hKK
      (by positivity : (0 : ℝ) ≤ 4 * (q - r).factorial)
    have hsub : ((q - r - 1 : ℕ) : ℝ) = ((q - r : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ q - r by omega), Nat.cast_one]
    have hh := rpow_margin_of_density_lower (γ := ((q - r : ℕ) : ℝ) - 1 / 3) (g := D) hn1
      (by positivity : (0 : ℝ) < 4 * (q - r).factorial)
      (by simpa only [Real.rpow_natCast] using hD)
      (C := (K : ℝ) ^ 2 + K) (α := ε / 3) (t := ρ) (u := ((q - r - 1 : ℕ) : ℝ))
      (by nlinarith only [hnum, hKKmul]) 2 (by rw [hsub]; norm_num; linarith only [hρ, hεhi])
    simpa only [Real.rpow_natCast] using hh
  refine ⟨hk, Real.rpow_pos_of_pos hn0 _, hF.error_half, ?_, ?_,
    hp₀, hp₁, hpow, hF.small, hF.denominator, hmany, by positivity, hcode⟩
  · exact (by positivity : (0 : ℝ) < (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial)).trans_le hg
  · exact (by positivity : (0 : ℝ) < (n : ℝ) ^ (((q - r : ℕ) : ℝ) - 1 / 3) /
      (4 * (q - r).factorial)).trans_le hD

theorem sparse_nibble_comparison_of_floor_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hk : 3 ≤ q.choose r) {ε : ℝ}
    (hε0 : 0 < ε) (hεhi : ε ≤ 2 / 5)
    (hF : NibbleFloorConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
      ((n : ℝ) ^ (-(ε / (3 * q.choose r)))))
    (hn : paperSizeThreshold q r ≤ n) {g D : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g)
    (hD : (n : ℝ) ^ (((q - r : ℕ) : ℝ) - 1 / 3) / (4 * (q - r).factorial) ≤ D) :
    NibbleComparisonParameters (q.choose r) ((n : ℝ) ^ (-(ε / 3 : ℝ))) g D
      ((n : ℝ) ^ (-(ε / (3 * q.choose r) : ℝ))) ((n : ℝ) ^ (q - r - 1)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hk0 : (q.choose r : ℝ) ≠ 0 := by exact_mod_cast (show q.choose r ≠ 0 by omega)
  have hpow : (n : ℝ) ^ (-(ε / 3)) ≤
      ((n : ℝ) ^ (-(ε / (3 * q.choose r)))) ^ (q.choose r) := by
    rw [← Real.rpow_mul_natCast hn0.le]
    apply le_of_eq
    congr 1
    field_simp
  exact sparse_nibble_comparison_at_floor_paper_threshold hr hqr hk hεhi
    (Real.rpow_pos_of_pos hn0 _)
    (Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (by positivity)))
    hpow hF hn hg hD

theorem sparse_nibble_comparison_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hk : 3 ≤ q.choose r) {ε : ℝ}
    (hεlo : 3 * (q.choose r : ℝ) * paperRho q r ≤ ε) (hεhi : ε ≤ 2 / 5)
    (hn : paperSizeThreshold q r ≤ n) {g D : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g)
    (hD : (n : ℝ) ^ (((q - r : ℕ) : ℝ) - 1 / 3) / (4 * (q - r).factorial) ≤ D) :
    NibbleComparisonParameters (q.choose r) ((n : ℝ) ^ (-(ε / 3 : ℝ))) g D
      ((n : ℝ) ^ (-(ε / (3 * q.choose r) : ℝ))) ((n : ℝ) ^ (q - r - 1)) := by
  exact sparse_nibble_comparison_of_floor_paper_threshold hr hqr hk
    (paper_sparse_nibble_floor_gaps hqr hk hεlo).1 hεhi
    (sparse_nibble_floor_paper_threshold hr hqr hk hεlo hn) hn hg hD

end Arxiv2411_18291
