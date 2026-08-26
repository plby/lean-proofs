/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Numerical parameters for exponential tails of local root counts.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LacunaryScale
import ErdosProblems.Erdos521.NormalizedLocalRoots

namespace Erdos521

theorem dyadic_local_jensen_term (j : ℕ) :
    24 / (((1 / 2 : ℝ) ^ j) ^ 2 * (4 : ℝ) ^ (2 * j)) = 24 * (1 / 4 : ℝ) ^ j := by
  have hden : ((1 / 2 : ℝ) ^ j) ^ 2 * (4 : ℝ) ^ (2 * j) = (4 : ℝ) ^ j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, pow_mul, ← mul_pow]
    norm_num
  rw [hden]
  rw [one_div_pow]
  ring

theorem dyadic_normalized_radius_le_lacunary (j : ℕ) (hj : 8 ≤ j) {V : ℝ}
    (hV : 0 ≤ V) (hVj : V ≤ j) :
    (1 / 2 : ℝ) ^ j * Real.sqrt V ≤ (1 / 4) * (1 / 8 : ℝ) ^ (j / 12) := by
  have hjpow : (j : ℝ) ≤ (2 : ℝ) ^ j := by
    exact_mod_cast (Nat.lt_two_pow_self (n := j)).le
  have he : 6 * (j / 12) + 4 ≤ j := by omega
  have hsq : ((1 / 2 : ℝ) ^ j * Real.sqrt V) ^ 2 ≤
      ((1 / 4) * (1 / 8 : ℝ) ^ (j / 12)) ^ 2 := by
    calc
      ((1 / 2 : ℝ) ^ j * Real.sqrt V) ^ 2 = (1 / 4 : ℝ) ^ j * V := by
        rw [mul_pow, Real.sq_sqrt hV, ← pow_mul, Nat.mul_comm j 2, pow_mul]
        norm_num
      _ ≤ (1 / 4 : ℝ) ^ j * (2 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left (hVj.trans hjpow) (by positivity)
      _ = (1 / 2 : ℝ) ^ j := by rw [← mul_pow]; norm_num
      _ ≤ (1 / 2 : ℝ) ^ (6 * (j / 12) + 4) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) he
      _ = ((1 / 4) * (1 / 8 : ℝ) ^ (j / 12)) ^ 2 := by
        have hpow : ((1 / 8 : ℝ) ^ (j / 12)) ^ 2 = ((1 / 8 : ℝ) ^ 2) ^ (j / 12) := by
          rw [← pow_mul, Nat.mul_comm (j / 12) 2, pow_mul]
        rw [pow_add, pow_mul, mul_pow, hpow]
        norm_num
        ring
  nlinarith [Real.sqrt_nonneg V, show 0 ≤ (1 / 4) * (1 / 8 : ℝ) ^ (j / 12) by positivity]

theorem half_degree_gap_lower (n j : ℕ) (hj : 1 ≤ j) {x : ℝ} (hx : 0 ≤ x)
    (hx₁ : x ≤ 1) (hgap : 32 * (j : ℝ) ≤ n * (1 - x)) :
    8 * (j : ℝ) ≤ (n / 2 : ℕ) * (1 - x) := by
  have hnR : 32 * (j : ℝ) ≤ n :=
    hgap.trans (mul_le_of_le_one_right (Nat.cast_nonneg n) (by linarith))
  have hn : 2 ≤ n := by
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hnR' : (2 : ℝ) ≤ n := by linarith
    exact_mod_cast hnR'
  have hhalf : (n : ℝ) ≤ 4 * (n / 2 : ℕ) := by
    exact_mod_cast (show n ≤ 4 * (n / 2) by omega)
  have hmul := mul_le_mul_of_nonneg_right hhalf (sub_nonneg.mpr hx₁)
  linarith

theorem half_degree_power_le (n j : ℕ) (hj : 1 ≤ j) {x : ℝ} (hx : 0 ≤ x)
    (hx₁ : x ≤ 1) (hgap : 32 * (j : ℝ) ≤ n * (1 - x)) :
    x ^ (n / 2) ≤ (1 / 2 : ℝ) ^ (3 * j) := by
  have hL := half_degree_gap_lower n j hj hx hx₁ hgap
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    x ^ (n / 2) ≤ Real.exp ((n / 2 : ℕ) * (-(1 - x))) :=
      pow_le_exp_nat_mul hx (by linarith) _
    _ ≤ Real.exp (-((3 * j : ℕ) : ℝ) * Real.log 2) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    _ = _ := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      simp only [one_div, inv_pow]

end Erdos521
