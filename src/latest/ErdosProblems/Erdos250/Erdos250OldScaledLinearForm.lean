import ErdosProblems.Erdos250.Erdos250OldDecay
import ErdosProblems.Erdos250.Erdos250ScaledDecay
import ErdosProblems.Erdos250.Erdos250QApery

open Filter
open scoped Topology

namespace OldScaledLinearForm

open Erdos250Arithmetic

noncomputable def E (n : ℕ) : ℕ :=
  2 ^ (n ^ 2 / 4) * denProd n ^ 2

def tri (n : ℕ) : ℕ := n * (n + 1) / 2

def halfSquare (n : ℕ) : ℕ := (n / 2) * (n / 2 + 1)

lemma twice_tri (n : ℕ) : 2 * tri n = n * (n + 1) := by
  exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)

lemma E_cast_le (n : ℕ) :
    (E n : ℝ) ≤ (2 : ℝ) ^ (n ^ 2 / 4 + 2 * tri n) := by
  have hd : (denProd n : ℝ) ≤ (2 : ℝ) ^ tri n := by
    exact_mod_cast OldDecayFull.denProd_le_pow_two_tri n
  rw [E]
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc
    (2 : ℝ) ^ (n ^ 2 / 4) * (denProd n : ℝ) ^ 2 ≤
        (2 : ℝ) ^ (n ^ 2 / 4) * ((2 : ℝ) ^ tri n) ^ 2 := by
      gcongr
    _ = (2 : ℝ) ^ (n ^ 2 / 4 + 2 * tri n) := by
      rw [← pow_mul, ← pow_add]
      congr 2 <;> omega

lemma abs_cast_lambda (n : ℕ) :
    |((VNormalization.lambda n : ℚ) : ℝ)| =
      (denProd n : ℝ) / (2 : ℝ) ^ (n ^ 2 + 2 * n + 1) := by
  rw [VNormalization.lambda]
  push_cast
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _), abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

lemma abs_cast_lambda_le (n : ℕ) :
    |((VNormalization.lambda n : ℚ) : ℝ)| ≤
      (2 : ℝ) ^ (((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ)) := by
  rw [abs_cast_lambda]
  have hd : (denProd n : ℝ) ≤ (2 : ℝ) ^ tri n := by
    exact_mod_cast OldDecayFull.denProd_le_pow_two_tri n
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
  exact div_le_div_of_nonneg_right hd (by positivity)

lemma exponent_le (n : ℕ) :
    (((n ^ 2 / 4 + 2 * tri n : ℕ) : ℤ) +
          ((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ) -
          ((n * (n + 1) : ℕ) : ℤ)) ≤
      -((halfSquare n : ℕ) : ℤ) := by
  have hsq : 4 * (n ^ 2 / 4) ≤ n ^ 2 := Nat.mul_div_le _ _
  have ht := twice_tri n
  have hn : n ≤ 2 * (n / 2) + 1 := by omega
  have hn' : 2 * (n / 2) ≤ n := by omega
  have hnat : n ^ 2 / 4 + 2 * tri n + tri n + halfSquare n ≤
      n ^ 2 + 2 * n + 1 + n * (n + 1) := by
    simp only [tri, halfSquare] at ht ⊢
    nlinarith
  have hnatZ :
      ((n ^ 2 / 4 + 2 * tri n + tri n + halfSquare n : ℕ) : ℤ) ≤
        ((n ^ 2 + 2 * n + 1 + n * (n + 1) : ℕ) : ℤ) := by
    exact_mod_cast hnat
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hnatZ ⊢
  omega

lemma scaled_abs_le {n : ℕ} (hn : 1 ≤ n) :
    (E n : ℝ) * |((VNormalization.lambda n : ℚ) : ℝ)| * QApery.S n ≤
      ((4 : ℝ) / 3) ^ (2 * n + 3) *
        (2 : ℝ) ^ (-((halfSquare n : ℕ) : ℤ)) := by
  have hE := E_cast_le n
  have hl := abs_cast_lambda_le n
  have hS := QApery.S_le_explicit hn
  have hS' : QApery.S n ≤
      ((4 : ℝ) / 3) ^ (2 * n + 3) *
        (2 : ℝ) ^ (-((n * (n + 1) : ℕ) : ℤ)) := by
    rw [show (2 : ℝ) ^ (-((n * (n + 1) : ℕ) : ℤ)) =
        QApery.q ^ (n * (n + 1)) by
          rw [show QApery.q = (2 : ℝ)⁻¹ by norm_num [QApery.q], inv_pow,
            zpow_neg, zpow_natCast]]
    exact hS
  calc
    (E n : ℝ) * |((VNormalization.lambda n : ℚ) : ℝ)| * QApery.S n ≤
        (2 : ℝ) ^ (n ^ 2 / 4 + 2 * tri n) *
          (2 : ℝ) ^ (((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ)) *
          (((4 : ℝ) / 3) ^ (2 * n + 3) *
            (2 : ℝ) ^ (-((n * (n + 1) : ℕ) : ℤ))) := by
      have hleft := mul_le_mul hE hl (abs_nonneg _)
        (by positivity : 0 ≤ (2 : ℝ) ^ (n ^ 2 / 4 + 2 * tri n))
      exact mul_le_mul hleft hS' (le_of_lt (QApery.S_pos hn))
        (mul_nonneg (by positivity) (by positivity))
    _ = ((4 : ℝ) / 3) ^ (2 * n + 3) *
          (2 : ℝ) ^
            (((n ^ 2 / 4 + 2 * tri n : ℕ) : ℤ) +
              ((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ) -
              ((n * (n + 1) : ℕ) : ℤ)) := by
      rw [show (2 : ℝ) ^ (n ^ 2 / 4 + 2 * tri n) =
          (2 : ℝ) ^ ((n ^ 2 / 4 + 2 * tri n : ℕ) : ℤ) by
            exact (zpow_natCast _ _).symm]
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [show (2 : ℝ) ^
          (((n ^ 2 / 4 + 2 * tri n : ℕ) : ℤ) +
            (((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ))) *
          (((4 : ℝ) / 3) ^ (2 * n + 3) *
            (2 : ℝ) ^ (-((n * (n + 1) : ℕ) : ℤ))) =
          ((4 : ℝ) / 3) ^ (2 * n + 3) *
            ((2 : ℝ) ^
              (((n ^ 2 / 4 + 2 * tri n : ℕ) : ℤ) +
                (((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ))) *
              (2 : ℝ) ^ (-((n * (n + 1) : ℕ) : ℤ))) by ring]
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 2 <;> ring
    _ ≤ ((4 : ℝ) / 3) ^ (2 * n + 3) *
          (2 : ℝ) ^ (-((halfSquare n : ℕ) : ℤ)) := by
      exact mul_le_mul_of_nonneg_left
        (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (exponent_le n))
        (by positivity)

theorem scaled_linear_form_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (E n : ℝ) * |((VNormalization.lambda n : ℚ) : ℝ)| * QApery.S n)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
      (le_of_lt (QApery.S_pos hn))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact scaled_abs_le hn
  · simpa [halfSquare] using tendsto_old_scaled_decay

end OldScaledLinearForm
