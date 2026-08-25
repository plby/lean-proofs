import ErdosProblems.Erdos157.TargetWindows
import ErdosProblems.Erdos157.MaskDecay

/-! A coarse summable bound after counting every target integer in a level window. -/

namespace Erdos157.Elementary

open AuxiliaryModuli Filter

theorem coefficientField_blockRadix_dyadic (i : ℕ) :
    blockRadix CoefficientField i ≤ 2 ^ (2068 * i + 1071) := by
  have hunit : Nat.card (ResidueField CoefficientField i)ˣ ≤
      Fintype.card CoefficientField ^ (2 * i + 1) := by
    rw [residueField_units_natCard, Nat.card_eq_fintype_card]
    exact Nat.sub_le _ _
  calc
    _ ≤ (2 ^ 7 * Fintype.card CoefficientField ^ (2 * i + 1)) *
        (2 ^ 10) ^ (2 * i + 4) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by decide) hunit) (Nat.pow_le_pow_left (by decide) _)
    _ = _ := by
      rw [card_coefficientField, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring

theorem coefficientField_initialPlace_dyadic (k : ℕ) :
    blockPlace CoefficientField 0 k ≤ 2 ^ (1034 * k ^ 2 + 37 * k) := by
  induction k with
  | zero => simp [blockPlace]
  | succ k ih =>
    rw [blockPlace_snoc]
    calc
      _ ≤ 2 ^ (1034 * k ^ 2 + 37 * k) * 2 ^ (2068 * k + 1071) :=
        Nat.mul_le_mul ih (coefficientField_blockRadix_dyadic k)
      _ = _ := by rw [← pow_add]; congr 1; ring

theorem coefficientField_windowCount_dyadic (k : ℕ) (hk : 1 ≤ k) :
    6 * blockPlace CoefficientField 0 (k + 1) ≤ 2 ^ (5000 * k ^ 2) := by
  calc
    _ ≤ 2 ^ 3 * 2 ^ (1034 * (k + 1) ^ 2 + 37 * (k + 1)) :=
      Nat.mul_le_mul (by decide) (coefficientField_initialPlace_dyadic (k + 1))
    _ = 2 ^ (3 + (1034 * (k + 1) ^ 2 + 37 * (k + 1))) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)

theorem sixth_le_two_pow_square (k : ℕ) (hk : 6 ≤ k) : k ^ 6 ≤ 2 ^ (k ^ 2) := by
  calc
    _ ≤ (2 ^ k) ^ 6 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ (6 * k) := by rw [← pow_mul, mul_comm k 6]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)

theorem eventually_window_failure_decay :
    ∀ᶠ k in atTop,
      (6 * blockPlace CoefficientField 0 (k + 1) : ℝ) * Real.exp (-(2 : ℝ) ^ (k ^ 2)) ≤
        Real.exp (-(k : ℝ)) := by
  let C := 5000 * Real.log 2
  filter_upwards [eventually_quadratic_sub_sixth_le_neg C, eventually_ge_atTop 6] with k hdec hk
  have hcount : (6 * blockPlace CoefficientField 0 (k + 1) : ℝ) ≤
      (2 : ℝ) ^ (5000 * k ^ 2) := by exact_mod_cast coefficientField_windowCount_dyadic k (by omega)
  have hpow : (k : ℝ) ^ 6 ≤ (2 : ℝ) ^ (k ^ 2) := by exact_mod_cast sixth_le_two_pow_square k hk
  have hcount' : (6 * blockPlace CoefficientField 0 (k + 1) : ℝ) ≤ Real.exp (C * (k : ℝ) ^ 2) := by
    have he : (2 : ℝ) ^ (5000 * k ^ 2) = Real.exp (C * (k : ℝ) ^ 2) := by
      rw [show C * (k : ℝ) ^ 2 = ((5000 * k ^ 2 : ℕ) : ℝ) * Real.log 2 by
        dsimp only [C]; push_cast; ring, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact hcount.trans_eq he
  calc
    _ ≤ Real.exp (C * (k : ℝ) ^ 2) * Real.exp (-(2 : ℝ) ^ (k ^ 2)) :=
      mul_le_mul_of_nonneg_right hcount' (Real.exp_pos _).le
    _ = Real.exp (C * (k : ℝ) ^ 2 - (2 : ℝ) ^ (k ^ 2)) := by rw [← Real.exp_add, sub_eq_add_neg]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 6])

end Erdos157.Elementary
