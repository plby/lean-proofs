import ErdosProblems.Erdos587.OneSixthPair

/-! The polynomial budget for the one-sixth smooth locator. -/

namespace Erdos587

lemma sixth_root_pow_six {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 6 : ℝ)) ^ 6 = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

lemma inverse_sixth_root_pow_six {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (-(1 / 6 : ℝ))) ^ 6 = x⁻¹ := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num [Real.rpow_neg_one]

lemma sqrt_pow_six {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x) ^ 6 = x ^ 3 := by
  calc
    _ = ((Real.sqrt x) ^ 2) ^ 3 := by ring
    _ = _ := by rw [Real.sq_sqrt hx]

theorem sixth_power_locator_budget {D F n δ : ℝ} (_hD : 0 ≤ D) (hF : 0 ≤ F)
    (hn : 0 < n) (hδ : 0 < δ) (hbudget : D ^ 6 * F < n ^ 3 * δ ^ 7) :
    D * F ^ (1 / 6 : ℝ) * Real.sqrt n * δ ^ (-(1 / 6 : ℝ)) < n * δ := by
  have hpower : (D * F ^ (1 / 6 : ℝ) * Real.sqrt n * δ ^ (-(1 / 6 : ℝ))) ^ 6 <
      (n * δ) ^ 6 := by
    rw [mul_pow, mul_pow, mul_pow, sixth_root_pow_six hF, sqrt_pow_six hn.le,
      inverse_sixth_root_pow_six hδ.le, mul_pow]
    have hh := mul_lt_mul_of_pos_right hbudget (div_pos (pow_pos hn 3) hδ)
    calc
      D ^ 6 * F * n ^ 3 * δ⁻¹ = (D ^ 6 * F) * (n ^ 3 / δ) := by ring
      _ < (n ^ 3 * δ ^ 7) * (n ^ 3 / δ) := hh
      _ = n ^ 6 * δ ^ 6 := by field_simp
  by_contra hnot
  have hle : n * δ ≤ D * F ^ (1 / 6 : ℝ) * Real.sqrt n * δ ^ (-(1 / 6 : ℝ)) :=
    le_of_not_gt hnot
  exact hpower.not_ge (pow_le_pow_left₀ (mul_pos hn hδ).le hle 6)

end Erdos587
