/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Power bounds for the window caps and residue-group count.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.WindowScales

namespace Erdos521

theorem windowWidthScale_pos {j : ℕ} (hj : 1 ≤ j) : 1 ≤ windowWidthScale j :=
  Nat.le_sqrt.mpr (Nat.le_sqrt.mpr hj)

theorem index_lt_windowCapScale_pow_eight (j : ℕ) : j < windowCapScale j ^ 8 := by
  have hq : windowWidthScale j + 1 ≤ windowCapScale j ^ 2 := by
    have h := Nat.lt_succ_sqrt' (windowWidthScale j)
    change windowWidthScale j < windowCapScale j ^ 2 at h
    omega
  calc
    j < (windowWidthScale j + 1) ^ 4 := index_lt_windowWidthScale_succ_pow_four j
    _ ≤ (windowCapScale j ^ 2) ^ 4 := pow_le_pow_left' hq 4
    _ = _ := by ring

theorem index_pow_four_le_windowCapScale_pow_thirtytwo (j : ℕ) :
    j ^ 4 ≤ windowCapScale j ^ 32 := by
  calc
    j ^ 4 ≤ (windowCapScale j ^ 8) ^ 4 := pow_le_pow_left' (index_lt_windowCapScale_pow_eight j).le 4
    _ = _ := by ring

theorem windowCapScale_sq_le {j : ℕ} (hj : 1 ≤ j) : windowCapScale j ^ 2 ≤ 4 * windowWidthScale j := by
  have hq := windowWidthScale_pos hj
  have hsmall := Nat.sqrt_le_self (windowWidthScale j)
  have hsq := Nat.sqrt_le' (windowWidthScale j)
  dsimp only [windowCapScale]
  nlinarith

theorem windowWidthScale_le_index (j : ℕ) : windowWidthScale j ≤ j :=
  (Nat.sqrt_le_self (Nat.sqrt j)).trans (Nat.sqrt_le_self j)

theorem windowCapScale_le_twice_index {j : ℕ} (hj : 1 ≤ j) : windowCapScale j ≤ 2 * j := by
  have h := (Nat.sqrt_le_self (windowWidthScale j)).trans (windowWidthScale_le_index j)
  dsimp only [windowCapScale]
  omega

theorem window_group_cap_parameter_le {j : ℕ} (hj : 1 ≤ j) :
    ((2 * windowWidthScale j + 1 : ℕ) : ℝ) ^ 2 * (windowCapScale j : ℝ) ^ 2 ≤
      36 * (windowWidthScale j : ℝ) ^ 3 := by
  have hq : (1 : ℝ) ≤ windowWidthScale j := by exact_mod_cast windowWidthScale_pos hj
  have hm : ((2 * windowWidthScale j + 1 : ℕ) : ℝ) ≤ 3 * (windowWidthScale j : ℝ) := by
    push_cast
    linarith
  have hT : (windowCapScale j : ℝ) ^ 2 ≤ 4 * (windowWidthScale j : ℝ) := by exact_mod_cast windowCapScale_sq_le hj
  calc
    _ ≤ (3 * (windowWidthScale j : ℝ)) ^ 2 * (4 * (windowWidthScale j : ℝ)) :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hm 2) hT (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

end Erdos521
