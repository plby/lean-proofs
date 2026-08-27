import Arxiv.Arxiv2411_18291.ExplicitNibbleComparison

/-! # Explicit clique-count and stopping conditions for the nibble -/

namespace Arxiv2411_18291

theorem nibble_count_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hk : 3 ≤ q.choose r) (hn : paperSizeThreshold q r ≤ n) {g D : ℝ}
    (hg : (n : ℝ) ^ r / (4 * r.factorial) ≤ g)
    (hD : (n : ℝ) ^ (q - r) / (4 * (q - r).factorial) ≤ D) :
    NibbleCountConditions (q.choose r) ((n : ℝ) ^ (-(1 / 9 : ℝ))) g D
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
  constructor
  · have hgap : ρ ≤ 2 * β := (paper_nibble_floor_gaps hqr hk).2.2
    have hβK : β * K = 1 / 9 := by dsimp only [β]; field_simp
    have hsub : ((K - 2 : ℕ) : ℝ) = (K : ℝ) - 2 := by
      rw [Nat.cast_sub (show 2 ≤ K by omega), Nat.cast_ofNat]
    have hh := paper_nibble_scaled_monomial (C := 128) (j := 0) (d := 0) hr hqr hn
      (by norm_num) (by norm_num) (by omega) (u := -(1 / 9)) (v := (-β) * (K - 2 : ℕ))
      (by rw [hsub]; nlinarith only [hgap, hβK])
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat, mul_one] at hh
    rw [Real.rpow_mul_natCast hn0.le] at hh
    exact hh.trans (le_mul_of_one_le_left (by positivity) (by linarith only [hkR]))
  · have hnum := paper_threshold_nibble_monomial (C := 4) (i := 0) (j := 0)
      (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    have hh := rpow_margin_of_density_lower (γ := (r : ℝ)) (g := g) hn1
      (by positivity : (0 : ℝ) < 4 * r.factorial)
      (by simpa only [Real.rpow_natCast] using hg)
      (C := 1) (α := 1 / 9) (t := ρ) (u := 0)
      (by simpa only [one_mul] using hnum) 3 (by norm_num; linarith only [hρ, hrR])
    simpa only [Real.rpow_zero, mul_one] using hh
  · have hnum := paper_threshold_nibble_monomial (C := 4) (i := 0) (j := 0)
      (d := q - r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) (Nat.sub_le _ _)
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    have hsub : ((q - r - 1 : ℕ) : ℝ) = ((q - r : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ q - r by omega), Nat.cast_one]
    have hh := rpow_margin_of_density_lower (γ := ((q - r : ℕ) : ℝ)) (g := D) hn1
      (by positivity : (0 : ℝ) < 4 * (q - r).factorial)
      (by simpa only [Real.rpow_natCast] using hD)
      (C := 1) (α := 1 / 9) (t := ρ) (u := ((q - r - 1 : ℕ) : ℝ))
      (by simpa only [one_mul] using hnum) 3 (by rw [hsub]; norm_num; linarith only [hρ])
    simpa only [Real.rpow_natCast, one_mul] using hh

theorem nibble_end_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hk : 3 ≤ q.choose r) (hn : paperSizeThreshold q r ≤ n) {g : ℝ}
    (hg : (n : ℝ) ^ r / (4 * r.factorial) ≤ g) :
    NibbleEndConditions (q.choose r) ((n : ℝ) ^ (-(1 / 9 : ℝ))) g n
      ((n : ℝ) ^ (-(1 / (9 * q.choose r) : ℝ))) (q - r + 1) := by
  let K := q.choose r
  let ρ := paperRho q r
  let β : ℝ := 1 / (9 * K)
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hρ : ρ ≤ 1 / 36 := paperRho_le_one_div_36 hqr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  constructor
  · have hnum := paper_threshold_nibble_monomial (C := 1056) (i := 0) (j := 3)
      (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    change 1056 * (K : ℝ) ^ 3 * r.factorial ≤ (n : ℝ) ^ ρ at hnum
    have hh := rpow_margin_of_density_lower (γ := (r : ℝ)) (g := g) hn1
      (by positivity : (0 : ℝ) < 4 * r.factorial)
      (by simpa only [Real.rpow_natCast] using hg)
      (C := 264 * (K : ℝ) ^ 3) (α := 1 / 9) (t := ρ) (u := 0)
      (by nlinarith only [hnum]) 3 (by norm_num; linarith only [hρ, hrR])
    simpa only [Real.rpow_zero, mul_one] using hh
  · have hnum := paper_threshold_nibble_monomial (C := 4) (i := 1) (j := 0)
      (d := 0) hr hqr hn (by norm_num) (by norm_num) (by norm_num) (by omega)
    simp only [pow_zero, pow_one, Nat.factorial_zero, Nat.cast_one,
      Nat.cast_ofNat, mul_one] at hnum
    have hdq : ((q - r + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast (show q - r + 1 ≤ q by omega)
    have hh := rpow_margin_of_density_lower (γ := 1) (g := (n : ℝ)) hn1
      (by norm_num : (0 : ℝ) < 1) (by simp only [Real.rpow_one, div_one, le_refl])
      (C := 4 * ((q - r + 1 : ℕ) : ℝ)) (α := 1 / 9) (t := ρ) (u := 0)
      (by nlinarith only [hnum, hdq]) 1 (by norm_num; linarith only [hρ])
    simpa only [Real.rpow_zero, mul_one, pow_one] using hh
  · have hgap : ρ + β ≤ 1 / 9 := (paper_nibble_floor_gaps hqr hk).2.1
    simpa only [pow_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_ofNat, mul_one] using
      paper_nibble_scaled_monomial (C := 128) (j := 1) (d := 0) hr hqr hn
        (by norm_num) (by norm_num) (by omega) (u := -(1 / 9)) (v := -β)
        (by linarith only [hgap])

end Arxiv2411_18291
