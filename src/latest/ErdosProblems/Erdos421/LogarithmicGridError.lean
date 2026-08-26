import ErdosProblems.Erdos421.PowerLogComparison

/-! # A logarithmic-size subdivision makes the kernel error negligible -/

namespace Erdos421

theorem logarithmic_grid_error_le {K L x ρ : ℝ} (hK : 0 ≤ K) (hL : 1 ≤ L)
    (hx : L ^ 2 ≤ x) (hρ : 0 ≤ ρ) (hρL : ρ ≤ (L ^ 2)⁻¹) :
    (⌈L ^ 2⌉₊ : ℝ) / L ^ 6 +
      6 * (K * (ρ + x⁻¹ + (⌈L ^ 2⌉₊ : ℝ)⁻¹)) ^ 2 ≤ (2 + 54 * K ^ 2) / L ^ 4 := by
  have hLp : 0 < L := by linarith
  have hL2 : 0 < L ^ 2 := sq_pos_of_pos hLp
  have hxp : 0 < x := hL2.trans_le hx
  have hceil := Nat.le_ceil (L ^ 2)
  have hNp : (0 : ℝ) < ⌈L ^ 2⌉₊ := hL2.trans_le hceil
  have hN : (⌈L ^ 2⌉₊ : ℝ) ≤ 2 * L ^ 2 := by
    have h := Nat.ceil_lt_add_one (sq_nonneg L)
    nlinarith
  have hxinv : x⁻¹ ≤ (L ^ 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hL2 hx
  have hNinv : (⌈L ^ 2⌉₊ : ℝ)⁻¹ ≤ (L ^ 2)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hL2 hceil
  have hsum : K * (ρ + x⁻¹ + (⌈L ^ 2⌉₊ : ℝ)⁻¹) ≤ 3 * K / L ^ 2 := by
    rw [div_eq_mul_inv]
    nlinarith
  have hs0 : 0 ≤ K * (ρ + x⁻¹ + (⌈L ^ 2⌉₊ : ℝ)⁻¹) := by positivity
  have hfirst : (⌈L ^ 2⌉₊ : ℝ) / L ^ 6 ≤ 2 / L ^ 4 := by
    calc
      _ ≤ (2 * L ^ 2) / L ^ 6 := div_le_div_of_nonneg_right hN (by positivity)
      _ = _ := by field_simp
  have hsecond : 6 * (K * (ρ + x⁻¹ + (⌈L ^ 2⌉₊ : ℝ)⁻¹)) ^ 2 ≤ 54 * K ^ 2 / L ^ 4 := by
    calc
      _ ≤ 6 * (3 * K / L ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hsum 2) (by norm_num)
      _ = _ := by field_simp; ring
  apply (add_le_add hfirst hsecond).trans_eq
  ring

end Erdos421
