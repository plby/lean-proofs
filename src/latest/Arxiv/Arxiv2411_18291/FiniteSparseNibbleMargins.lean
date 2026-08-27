import Arxiv.Arxiv2411_18291.ExplicitNibbleBinomial

/-! # Finite margins for variable-error nibble with polynomially sparse densities -/

namespace Arxiv2411_18291

theorem sparse_nibble_error_lower_eq {q r : ℕ} (hqr : r < q) :
    3 * (q.choose r : ℝ) * paperRho q r = 1 / (12 * (q.choose r : ℝ)) := by
  have hk : (q.choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hqr.le).ne'
  unfold paperRho
  field_simp
  ring

theorem paper_sparse_nibble_floor_gaps {q r : ℕ} (hqr : r < q)
    (hk : 3 ≤ q.choose r) {ε : ℝ}
    (hε : 3 * (q.choose r : ℝ) * paperRho q r ≤ ε) :
    let β := ε / (3 * (q.choose r : ℝ))
    0 < ε ∧ paperRho q r ≤ β ∧ paperRho q r + 2 * β ≤ ε / 3 ∧
      paperRho q r + β ≤ ε / 3 ∧ paperRho q r ≤ 2 * β := by
  dsimp only
  have hkR : (3 : ℝ) ≤ q.choose r := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < q.choose r := by linarith only [hkR]
  have hρ := paperRho_pos hqr
  have hε0 : 0 < ε := (by positivity : (0 : ℝ) <
    3 * (q.choose r : ℝ) * paperRho q r).trans_le hε
  have hβ : paperRho q r ≤ ε / (3 * (q.choose r : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hε]
  have hβ0 : 0 < ε / (3 * (q.choose r : ℝ)) := by positivity
  have heq : (q.choose r : ℝ) * (ε / (3 * (q.choose r : ℝ))) = ε / 3 := by
    field_simp
  have hthree := mul_le_mul_of_nonneg_right hkR hβ0.le
  exact ⟨hε0, hβ, by nlinarith only [heq, hthree, hβ],
    by nlinarith only [heq, hthree, hβ, hβ0], by linarith only [hβ, hβ0]⟩

theorem binomial_density_lower_paper_threshold {q r n d : ℕ}
    (hr : 1 ≤ r) (hqr : r < q) (hn : paperSizeThreshold q r ≤ n) (hd : d ≤ q)
    {β φ : ℝ} (hφ : (n : ℝ) ^ (-β) ≤ φ) :
    (n : ℝ) ^ ((d : ℝ) - β) / (2 * d.factorial) ≤ φ * (n.choose d : ℝ) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hφ0 : 0 ≤ φ := (Real.rpow_nonneg hn0.le _).trans hφ
  have hchoose := paper_threshold_choose_ge_half_power hr hqr hn hd
  calc
    _ = (n : ℝ) ^ (-β) * ((n : ℝ) ^ d / (2 * d.factorial)) := by
      rw [← mul_div_assoc, ← Real.rpow_natCast (n : ℝ) d, ← Real.rpow_add hn0]
      congr 2
      ring
    _ ≤ _ := mul_le_mul hφ hchoose (by positivity) hφ0

end Arxiv2411_18291
