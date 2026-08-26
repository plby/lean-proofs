/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Fourth-root window widths and eighth-root caps along dyadic degrees.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SqrtScales

namespace Erdos521

open Filter
open scoped Topology

def windowWidthScale (j : ℕ) : ℕ := Nat.sqrt (Nat.sqrt j)

def windowCapScale (j : ℕ) : ℕ := Nat.sqrt (windowWidthScale j) + 1

theorem windowWidthScale_pow_four_le (j : ℕ) : windowWidthScale j ^ 4 ≤ j := by
  calc
    windowWidthScale j ^ 4 = (Nat.sqrt (Nat.sqrt j) ^ 2) ^ 2 := by simp [windowWidthScale, ← pow_mul]
    _ ≤ Nat.sqrt j ^ 2 := pow_le_pow_left' (Nat.sqrt_le' (Nat.sqrt j)) 2
    _ ≤ j := Nat.sqrt_le' j

theorem index_lt_windowWidthScale_succ_pow_four (j : ℕ) : j < (windowWidthScale j + 1) ^ 4 := by
  have hr : Nat.sqrt j + 1 ≤ (windowWidthScale j + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' (Nat.sqrt j)
    change Nat.sqrt j < (windowWidthScale j + 1) ^ 2 at h
    omega
  calc
    j < (Nat.sqrt j + 1) ^ 2 := Nat.lt_succ_sqrt' j
    _ ≤ ((windowWidthScale j + 1) ^ 2) ^ 2 := pow_le_pow_left' hr 2
    _ = _ := by ring

theorem real_fourth_root_pow_four (j : ℕ) : ((j : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = j := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg j)]
  norm_num

theorem windowWidthScale_cast_le (j : ℕ) : (windowWidthScale j : ℝ) ≤ (j : ℝ) ^ (1 / 4 : ℝ) := by
  have hq : (windowWidthScale j : ℝ) ^ 4 ≤ j := by exact_mod_cast windowWidthScale_pow_four_le j
  have hq₂ : (windowWidthScale j : ℝ) ^ 2 ≤ ((j : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
    apply (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mp
    nlinarith [real_fourth_root_pow_four j]
  exact (sq_le_sq₀ (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)).mp hq₂

theorem windowWidthScale_lower_half {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) ^ (1 / 4 : ℝ) / 2 ≤ (windowWidthScale j : ℝ) := by
  have hq : 1 ≤ windowWidthScale j := Nat.le_sqrt.mpr (Nat.le_sqrt.mpr hj)
  have hq₁ : (1 : ℝ) ≤ windowWidthScale j := by exact_mod_cast hq
  have hpow : (j : ℝ) < ((windowWidthScale j : ℝ) + 1) ^ 4 := by
    exact_mod_cast index_lt_windowWidthScale_succ_pow_four j
  have hroot₂ : ((j : ℝ) ^ (1 / 4 : ℝ)) ^ 2 < ((windowWidthScale j : ℝ) + 1) ^ 2 := by
    apply (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mp
    nlinarith [real_fourth_root_pow_four j]
  have hroot := (sq_lt_sq₀ (Real.rpow_nonneg (Nat.cast_nonneg j) _) (by positivity)).mp hroot₂
  linarith

theorem windowWidthScale_tendsto_atTop : Tendsto windowWidthScale atTop atTop :=
  nat_sqrt_tendsto_atTop.comp nat_sqrt_tendsto_atTop

theorem eventually_two_pow_neg_windowWidth_le (p : ℝ) :
    ∀ᶠ j : ℕ in atTop, ((2 : ℝ) ^ windowWidthScale j)⁻¹ ≤ (j : ℝ) ^ p := by
  have hc : 0 < Real.log 2 / 2 := by positivity
  filter_upwards [eventually_exp_neg_rpow_le_rpow hc (by norm_num : (0 : ℝ) < 1 / 4) p,
    eventually_ge_atTop 1] with j hj hj₁
  apply le_trans _ hj
  have heq : ((2 : ℝ) ^ windowWidthScale j)⁻¹ = Real.exp (-(windowWidthScale j : ℝ) * Real.log 2) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [heq]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (windowWidthScale_lower_half hj₁)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  nlinarith

end Erdos521
