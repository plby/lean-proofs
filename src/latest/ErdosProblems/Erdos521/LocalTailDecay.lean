/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A single exponential bound for the local root-count tail.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LocalRootTail

namespace Erdos521

theorem half_pow_le_exp (j : ℕ) : (1 / 2 : ℝ) ^ j ≤ Real.exp (-(j : ℝ) / 2) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  calc
    (1 / 2 : ℝ) ^ j = Real.exp (-(j : ℝ) * Real.log 2) := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      simp only [one_div, inv_pow]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
      linarith

theorem quarter_floor_pow_le_exp (j : ℕ) :
    (1 / 4 : ℝ) ^ (j / 12) ≤ 4 * Real.exp (-(j : ℝ) / 24) := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 4)
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
    linarith
  have hfloor : (j : ℝ) ≤ 12 * (j / 12 : ℕ) + 12 := by
    exact_mod_cast (show j ≤ 12 * (j / 12) + 12 by omega)
  calc
    (1 / 4 : ℝ) ^ (j / 12) = Real.exp (-(j / 12 : ℕ) * Real.log 4) := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      simp only [one_div, inv_pow]
    _ ≤ Real.exp (Real.log 4 - (j : ℝ) / 24) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hfloor (by linarith : 0 ≤ Real.log 4)
      have h' := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
      nlinarith
    _ = _ := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4), neg_div, Real.exp_neg]
      rfl

noncomputable def localTailRate : ℝ := min (1 / (4 * Real.pi ^ 2)) (1 / 24)

noncomputable def localTailConstant : ℝ :=
  Real.exp (1 / 2) * (Real.sqrt (Real.pi / (1 / (4 * Real.pi ^ 2))) + 3) + 28

theorem localTailRate_pos : 0 < localTailRate := by
  unfold localTailRate
  positivity

theorem localTailConstant_pos : 0 < localTailConstant := by
  unfold localTailConstant
  positivity

theorem localTailBound_le_exp (j : ℕ) :
    localTailBound j ≤ localTailConstant * Real.exp (-localTailRate * j) := by
  have hd₁ : localTailRate ≤ 1 / (4 * Real.pi ^ 2) := min_le_left _ _
  have hd₂ : localTailRate ≤ 1 / 24 := min_le_right _ _
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hhalf : Real.exp (-(j : ℝ) / 2) ≤ Real.exp (-localTailRate * j) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfloor : Real.exp (-(j : ℝ) / 24) ≤ Real.exp (-localTailRate * j) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hvar : Real.exp (-(1 / (4 * Real.pi ^ 2)) * j) ≤ Real.exp (-localTailRate * j) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpow := (half_pow_le_exp j).trans hhalf
  have hquarter := (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) j).trans hpow
  have hfloorpow := (quarter_floor_pow_le_exp j).trans (mul_le_mul_of_nonneg_left hfloor (by norm_num))
  have hweighted := mul_le_mul_of_nonneg_right hpow
    (Real.sqrt_nonneg (Real.pi / (1 / (4 * Real.pi ^ 2))))
  have hsum := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hweighted hvar)
    (mul_le_mul_of_nonneg_left hhalf (by norm_num : (0 : ℝ) ≤ 2))) (Real.exp_pos (1 / 2)).le
  dsimp only [localTailBound, localTailConstant]
  nlinarith

theorem localRootCount_exponential_tail (n j : ℕ) (hj : 8 ≤ j) {x : ℝ}
    (hx : 9 / 10 ≤ x) (hx₁ : x < 1) (hgap : 32 * (j : ℝ) ≤ n * (1 - x)) :
    sequenceLaw.real {ε | 2 * j ≤ localRootCount ε n x ((1 - x) / 8)} ≤
      localTailConstant * Real.exp (-localTailRate * j) :=
  (localRootCount_tail n j hj hx hx₁ hgap).trans (localTailBound_le_exp j)

end Erdos521
