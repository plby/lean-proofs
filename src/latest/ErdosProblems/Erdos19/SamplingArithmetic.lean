import ErdosProblems.Erdos76.PippengerSpencerParameters

/-! # A union bound for degree and cut constraints -/

namespace Erdos19

theorem exists_linear_quadratic_tail_budget (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 * (n : ℝ) * Real.exp (-c * n) +
        2 * (4 : ℝ) ^ n * Real.exp (-c * (n : ℝ) ^ 2) < 1 := by
  obtain ⟨N₀, hN₀⟩ :=
    Erdos76.PippengerSpencerParameters.exists_exp_tail_mul_polynomial_le_one c 2 1 hc
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge ((2 + c) / c)
  refine ⟨max N₀ (max N₁ 1), ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hratio : (2 + c) / c ≤ n := hN₁.trans (by exact_mod_cast
    (le_trans (le_max_left N₁ 1) (le_trans (le_max_right N₀ (max N₁ 1)) hn)))
  have hcn : 2 + c ≤ c * n := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hratio
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have hx := Real.add_one_le_exp (1 : ℝ)
    have he : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he]
    nlinarith only [hx]
  have h4n : (4 : ℝ) ^ n ≤ Real.exp (2 * n) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4 n
    simpa only [← Real.exp_nat_mul, mul_comm] using hp
  have hquad : (4 : ℝ) ^ n * Real.exp (-c * (n : ℝ) ^ 2) ≤ Real.exp (-c * n) := by
    calc
      (4 : ℝ) ^ n * Real.exp (-c * (n : ℝ) ^ 2) ≤
          Real.exp (2 * n) * Real.exp (-c * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right h4n (Real.exp_nonneg _)
      _ = Real.exp (2 * n - c * (n : ℝ) ^ 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-c * n) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_left hcn hnR.le]
  calc
    2 * (n : ℝ) * Real.exp (-c * n) +
        2 * (4 : ℝ) ^ n * Real.exp (-c * (n : ℝ) ^ 2) ≤
      2 * (n : ℝ) * Real.exp (-c * n) + 2 * Real.exp (-c * n) := by
        linarith
    _ = 2 * Real.exp (-c * n) * ((n : ℝ) + 1) := by ring
    _ < 2 * Real.exp (-c * n) * (2 * (n : ℝ) + 1) := by
      apply mul_lt_mul_of_pos_left (by linarith)
      positivity
    _ ≤ 1 := by simpa only [pow_one] using hN₀ n ((le_max_left _ _).trans hn)

#print axioms exists_linear_quadratic_tail_budget

end Erdos19
