import Arxiv.Arxiv2411_18291.FiniteSparseNibbleComparison

/-! # Finite count and stopping conditions for the sparse, variable-error nibble -/

namespace Arxiv2411_18291

theorem sparse_nibble_count_at_floor_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    {ε p₀ : ℝ} (hεhi : ε ≤ 2 / 5)
    (hF : NibbleFloorConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
      p₀)
    (hn : paperSizeThreshold q r ≤ n) {g D : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g)
    (hD : (n : ℝ) ^ (((q - r : ℕ) : ℝ) - 1 / 3) / (4 * (q - r).factorial) ≤ D) :
    NibbleCountConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3 : ℝ))) g D
      p₀ ((n : ℝ) ^ (q - r - 1)) := by
  let ρ := paperRho q r
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hρ : ρ ≤ 1 / 36 := paperRho_le_one_div_36 hqr
  refine ⟨hF.variance_bound, ?_, ?_⟩
  · have hnum := paper_threshold_nibble_monomial (C := 4) (i := 0) (j := 0)
      (d := r) hr hqr hn (by norm_num) (by norm_num) (by norm_num) hqr.le
    simp only [pow_zero, mul_one, Nat.cast_ofNat] at hnum
    have hh := rpow_margin_of_density_lower (γ := (19 / 20 : ℝ)) (g := g) hn1
      (by positivity : (0 : ℝ) < 4 * r.factorial)
      (by simpa only [Real.rpow_natCast] using hg)
      (C := 1) (α := ε / 3) (t := ρ) (u := 0)
      (by simpa only [one_mul] using hnum) 3 (by norm_num; linarith only [hρ, hεhi])
    simpa only [Real.rpow_zero, mul_one] using hh
  · have hnum := paper_threshold_nibble_monomial (C := 4) (i := 0) (j := 0)
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

theorem sparse_nibble_count_of_floor_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (hF : NibbleFloorConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
      ((n : ℝ) ^ (-(ε / (3 * q.choose r)))))
    (hn : paperSizeThreshold q r ≤ n) {g D : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g)
    (hD : (n : ℝ) ^ (((q - r : ℕ) : ℝ) - 1 / 3) / (4 * (q - r).factorial) ≤ D) :
    NibbleCountConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3 : ℝ))) g D
      ((n : ℝ) ^ (-(ε / (3 * q.choose r) : ℝ))) ((n : ℝ) ^ (q - r - 1)) := by
  exact sparse_nibble_count_at_floor_paper_threshold hr hqr hεhi hF hn hg hD

theorem sparse_nibble_end_at_floor_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    {ε p₀ : ℝ} (hεhi : ε ≤ 2 / 5)
    (hF : NibbleFloorConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
      p₀)
    (hn : paperSizeThreshold q r ≤ n) {g : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g) :
    NibbleEndConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3 : ℝ))) g n
      p₀ (q - r + 1) := by
  let K := q.choose r
  let ρ := paperRho q r
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hρ : ρ ≤ 1 / 36 := paperRho_le_one_div_36 hqr
  refine ⟨?_, ?_, hF.face_error⟩
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

theorem sparse_nibble_end_of_floor_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (hF : NibbleFloorConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3)))
      ((n : ℝ) ^ (-(ε / (3 * q.choose r)))))
    (hn : paperSizeThreshold q r ≤ n) {g : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g) :
    NibbleEndConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3 : ℝ))) g n
      ((n : ℝ) ^ (-(ε / (3 * q.choose r) : ℝ))) (q - r + 1) := by
  exact sparse_nibble_end_at_floor_paper_threshold hr hqr hεhi hF hn hg

theorem sparse_nibble_count_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hk : 3 ≤ q.choose r) {ε : ℝ}
    (hεlo : 3 * (q.choose r : ℝ) * paperRho q r ≤ ε) (hεhi : ε ≤ 2 / 5)
    (hn : paperSizeThreshold q r ≤ n) {g D : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g)
    (hD : (n : ℝ) ^ (((q - r : ℕ) : ℝ) - 1 / 3) / (4 * (q - r).factorial) ≤ D) :
    NibbleCountConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3 : ℝ))) g D
      ((n : ℝ) ^ (-(ε / (3 * q.choose r) : ℝ))) ((n : ℝ) ^ (q - r - 1)) := by
  exact sparse_nibble_count_of_floor_paper_threshold hr hqr hεhi
    (sparse_nibble_floor_paper_threshold hr hqr hk hεlo hn) hn hg hD

theorem sparse_nibble_end_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hk : 3 ≤ q.choose r) {ε : ℝ}
    (hεlo : 3 * (q.choose r : ℝ) * paperRho q r ≤ ε) (hεhi : ε ≤ 2 / 5)
    (hn : paperSizeThreshold q r ≤ n) {g : ℝ}
    (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * r.factorial) ≤ g) :
    NibbleEndConditions (q.choose r) ((n : ℝ) ^ (-(ε / 3 : ℝ))) g n
      ((n : ℝ) ^ (-(ε / (3 * q.choose r) : ℝ))) (q - r + 1) := by
  exact sparse_nibble_end_of_floor_paper_threshold hr hqr hεhi
    (sparse_nibble_floor_paper_threshold hr hqr hk hεlo hn) hn hg

end Arxiv2411_18291
