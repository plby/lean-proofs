import ErdosProblems.Erdos421.DivisorSquares
import ErdosProblems.Erdos421.FiniteCoefficients
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # First and second moments of divisor coefficients -/

namespace Erdos421

theorem divisorTuples_weighted_sum_le (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (divisorTuples k n : ℝ) / n) ≤ (harmonic X : ℝ) ^ k := by
  by_cases hX : X = 0
  · subst X
    simp
  have hXpos : 0 < X := Nat.pos_of_ne_zero hX
  have hXone : 1 ≤ X := hXpos
  cases k with
  | zero => simp [divisorTuples_zero, ite_div, hXone]
  | succ k =>
    let f := arithmeticTruncate ArithmeticFunction.zeta X
    have hf : SupportedThrough f X := arithmeticTruncate_supported _ _
    have hbase : (∑ n ∈ Finset.Icc 1 X, (f n : ℝ) / n) = (harmonic X : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hn₁, hnX⟩ := Finset.mem_Icc.mp hn
      have hn0 : n ≠ 0 := by omega
      simp only [f, arithmeticTruncate_apply, if_pos hnX,
        ArithmeticFunction.zeta_apply_ne hn0, Nat.cast_one, one_div]
    have hXpow : X ≤ X ^ (k + 1) := by
      calc
        X = X * 1 := (mul_one X).symm
        _ ≤ X * X ^ k := Nat.mul_le_mul_left X (one_le_pow₀ hXone)
        _ = X ^ (k + 1) := (pow_succ' X k).symm
    calc
      _ = ∑ n ∈ Finset.Icc 1 X, ((f ^ (k + 1) : ArithmeticFunction ℕ) n : ℝ) / n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [arithmeticTruncate_pow_apply _ _ _ (Finset.mem_Icc.mp hn).2]
        rfl
      _ ≤ ∑ n ∈ Finset.Icc 1 (X ^ (k + 1)),
          ((f ^ (k + 1) : ArithmeticFunction ℕ) n : ℝ) / n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
            (Finset.mem_Icc.mp hn).2.trans hXpow⟩
        · intro n _ _
          positivity
      _ = (harmonic X : ℝ) ^ (k + 1) := by rw [hf.weighted_sum_pow, hbase]

theorem divisorTuples_sum_le (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (divisorTuples k n : ℝ)) ≤ X * (harmonic X : ℝ) ^ k := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (X : ℝ) * ((divisorTuples k n : ℝ) / n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnX : (n : ℝ) ≤ X := by exact_mod_cast (Finset.mem_Icc.mp hn).2
      calc
        _ = (n : ℝ) * ((divisorTuples k n : ℝ) / n) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hnX (by positivity)
    _ = (X : ℝ) * (∑ n ∈ Finset.Icc 1 X, (divisorTuples k n : ℝ) / n) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (divisorTuples_weighted_sum_le k X) (Nat.cast_nonneg X)

theorem divisorTuples_square_sum_le (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (divisorTuples k n : ℝ) ^ 2) ≤
      X * (harmonic X : ℝ) ^ (k ^ 2) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (divisorTuples (k ^ 2) n : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      exact_mod_cast divisorTuples_square_le k n
    _ ≤ _ := divisorTuples_sum_le _ _

theorem divisorTuples_square_sum_log_le (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (divisorTuples k n : ℝ) ^ 2) ≤
      X * (1 + Real.log X) ^ (k ^ 2) := by
  refine (divisorTuples_square_sum_le k X).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
  have hH : (0 : ℝ) ≤ harmonic X := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ ↦ by positivity)
  exact pow_le_pow_left₀ hH (harmonic_le_one_add_log X) _

theorem convolution_pow_energy_bound (f : ArithmeticFunction ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, n ≠ 0 → ‖f n‖ ≤ C) (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ‖(f ^ k : ArithmeticFunction ℂ) n‖ ^ 2) ≤
      C ^ (2 * k) * X * (1 + Real.log X) ^ (k ^ 2) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (C ^ k * divisorTuples k n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_convolution_pow_le f hC hf k n) 2
    _ = C ^ (2 * k) * (∑ n ∈ Finset.Icc 1 X, (divisorTuples k n : ℝ) ^ 2) := by
      simp only [mul_pow, ← pow_mul, Nat.mul_comm k 2, Finset.mul_sum]
    _ ≤ C ^ (2 * k) * (X * (1 + Real.log X) ^ (k ^ 2)) :=
      mul_le_mul_of_nonneg_left (divisorTuples_square_sum_log_le k X) (pow_nonneg hC _)
    _ = _ := by ring

end Erdos421
