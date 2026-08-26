import ErdosProblems.Erdos1148.CuspRunGeometry

/-! # Absorbing the number of cusp runs into a small exponential overhead -/

namespace Erdos1148.DukeArithmetic

theorem fixed_pattern_cost_exp_bound {K H : ℝ} (hK : 1 ≤ K) (hH : 1 < H)
    (n v r : ℕ) (hr : (r : ℝ) ≤ (n : ℝ) / (4 * Real.log H) + 1) :
    K ^ (2 * r + 1) * Real.exp ((n : ℝ) + 4 * Real.log H - ((v : ℝ) - r) / 2) ≤
      Real.exp (3 * Real.log K + 4 * Real.log H + 1 / 2) *
        Real.exp ((1 + (2 * Real.log K + 1 / 2) / (4 * Real.log H)) * n - (v : ℝ) / 2) := by
  have hKpos : 0 < K := by linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hp : K ^ (2 * r + 1) = Real.exp ((2 * (r : ℝ) + 1) * Real.log K) := by
    calc
      _ = Real.exp (((2 * r + 1 : ℕ) : ℝ) * Real.log K) := by
        rw [Real.exp_nat_mul, Real.exp_log hKpos]
      _ = _ := by push_cast; rfl
  rw [hp, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hscaled := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 2 * Real.log K + 1 / 2 by linarith)
  have hscaled' : (2 * Real.log K + 1 / 2) * (r : ℝ) ≤
      ((2 * Real.log K + 1 / 2) / (4 * Real.log H)) * n + (2 * Real.log K + 1 / 2) := by
    calc
      _ ≤ (2 * Real.log K + 1 / 2) * ((n : ℝ) / (4 * Real.log H) + 1) := hscaled
      _ = _ := by ring
  nlinarith [hscaled']

theorem fixed_pattern_cost_small_rate {K H ε : ℝ} (hK : 1 ≤ K) (hH : 1 < H)
    (hrate : (2 * Real.log K + 1 / 2) / (4 * Real.log H) ≤ ε)
    (n v r : ℕ) (hr : (r : ℝ) ≤ (n : ℝ) / (4 * Real.log H) + 1) :
    K ^ (2 * r + 1) * Real.exp ((n : ℝ) + 4 * Real.log H - ((v : ℝ) - r) / 2) ≤
      Real.exp (3 * Real.log K + 4 * Real.log H + 1 / 2) *
        Real.exp ((1 + ε) * n - (v : ℝ) / 2) := by
  apply (fixed_pattern_cost_exp_bound hK hH n v r hr).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg n : (0 : ℝ) ≤ _)]

end Erdos1148.DukeArithmetic
