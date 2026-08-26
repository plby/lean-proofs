/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Logarithmic choice of the grid index in the repulsion estimate.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RepulsionGrid

namespace Erdos521

open Filter

noncomputable def repulsionIndex (A : ℝ) (n : ℕ) : ℕ := ⌊A * Real.log n⌋₊

theorem repulsionIndex_le {A : ℝ} (hA : 0 ≤ A) {n : ℕ} (hn : 1 ≤ n) :
    (repulsionIndex A n : ℝ) ≤ A * Real.log n := by
  exact Nat.floor_le (mul_nonneg hA (Real.log_nonneg (by exact_mod_cast hn)))

theorem half_pow_repulsionIndex_le (A : ℝ) {n : ℕ} (hn : 0 < n) :
    (1 / 2 : ℝ) ^ repulsionIndex A n ≤ 2 * (n : ℝ) ^ (-A * Real.log 2) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor : A * Real.log n - 1 ≤ (repulsionIndex A n : ℝ) :=
    (Nat.sub_one_lt_floor (A * Real.log n)).le
  have hlhs : (1 / 2 : ℝ) ^ repulsionIndex A n =
      Real.exp (-((repulsionIndex A n : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      one_div_pow, one_div]
  have hrhs : 2 * (n : ℝ) ^ (-A * Real.log 2) =
      Real.exp (Real.log 2 + Real.log n * (-A * Real.log 2)) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hn₀]
  rw [hlhs, hrhs]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hfloor hlog₂.le
  nlinarith

theorem repulsionThreshold_index_lower {A : ℝ} (hA : 0 ≤ A) {n : ℕ} (hn : 1 ≤ n) :
    (1 / 16) * (n : ℝ) ^ (-2 * A * Real.log 8) ≤ repulsionThreshold (repulsionIndex A n) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfloor := repulsionIndex_le hA hn
  have hlog₈ : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hη : repulsionThreshold (repulsionIndex A n) = (1 / 16) *
      Real.exp (-(((2 * repulsionIndex A n : ℕ) : ℝ) * Real.log 8)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
    unfold repulsionThreshold
    ring
  rw [hη, Real.rpow_def_of_pos hn₀]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 16)
  apply Real.exp_le_exp.mpr
  push_cast
  have h := mul_le_mul_of_nonneg_right hfloor hlog₈.le
  nlinarith

theorem repulsion_grid_probability_factor_le (n j : ℕ) :
    (repulsionMesh n j + 1 : ℕ) * (1 / 4 : ℝ) ^ (2 * j) ≤
      (8 * (n + 1 : ℝ) ^ 2 + 1) * (1 / 2 : ℝ) ^ j := by
  have hproduct : (8 : ℝ) ^ j * (1 / 16 : ℝ) ^ j = (1 / 2 : ℝ) ^ j := by
    rw [← mul_pow]
    norm_num
  have hsmall : (1 / 16 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  simp only [repulsionMesh, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat,
    pow_mul, show (1 / 4 : ℝ) ^ 2 = 1 / 16 by norm_num]
  calc
    _ = 8 * (n + 1 : ℝ) ^ 2 * ((8 : ℝ) ^ j * (1 / 16 : ℝ) ^ j) + (1 / 16 : ℝ) ^ j := by ring
    _ ≤ 8 * (n + 1 : ℝ) ^ 2 * (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j := by
      rw [hproduct]
      exact add_le_add le_rfl hsmall
    _ = _ := by ring

theorem eventually_rpow_le_repulsionThreshold {A B : ℝ} (hA : 0 ≤ A)
    (hB : 2 * A * Real.log 8 < B) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-B) ≤ repulsionThreshold (repulsionIndex A n) := by
  filter_upwards [eventually_const_mul_rpow_le_rpow (C := 16)
    (by linarith : -B < -2 * A * Real.log 8), eventually_ge_atTop 1] with n h hn
  apply le_trans _ (repulsionThreshold_index_lower hA hn)
  linarith

end Erdos521
