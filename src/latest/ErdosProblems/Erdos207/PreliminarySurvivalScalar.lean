/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupplyStoppedGreedyJointLaw

/-!
# A uniform scalar survival estimate for the preliminary process

If the available family has size at most `M` and every prescribed residual
edge rules out at least `3 * k` choices, then the one-step survival ratio is
at most `((M-k)/M)^b` for `b` prescribed residual edges.  The proof is the
elementary Bernoulli inequality, with the natural-number truncation treated
explicitly.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

/-- The scalar inequality used to turn a local choice floor into a uniform
geometric survival factor. -/
theorem nat_sub_mul_inv_le_sub_ratio_pow
    (A M k b : ℕ) (hA : 0 < A) (hAM : A ≤ M) (hkM : k ≤ M) :
    ((A - b * k : ℕ) : ℝ≥0) * (A : ℝ≥0)⁻¹ ≤
      (((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^ b := by
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_natCast,
    NNReal.coe_pow]
  have hM : 0 < M := lt_of_lt_of_le hA hAM
  by_cases hbkA : b * k ≤ A
  · rw [Nat.cast_sub hbkA, Nat.cast_mul, Nat.cast_sub hkM]
    have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
    have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
    have hkMreal : (k : ℝ) ≤ M := by exact_mod_cast hkM
    have hratio : (k : ℝ) / M ≤ 1 := (div_le_one hMreal).2 hkMreal
    have hlinear :
        ((A : ℝ) - (b : ℝ) * k) * (A : ℝ)⁻¹ ≤
          1 - (b : ℝ) * ((k : ℝ) / M) := by
      rw [← div_eq_mul_inv]
      have hratio_mono : (k : ℝ) / M ≤ (k : ℝ) / A := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact_mod_cast hA
        · exact_mod_cast hAM
      rw [sub_div, div_self (ne_of_gt hAreal)]
      have hmulratio :=
        mul_le_mul_of_nonneg_left hratio_mono (Nat.cast_nonneg b)
      have hrewrite : (b : ℝ) * ((k : ℝ) / A) =
          (b : ℝ) * k / A := by ring
      rw [hrewrite] at hmulratio
      linarith
    have hbern :
        1 - (b : ℝ) * ((k : ℝ) / M) ≤
          (1 - (k : ℝ) / M) ^ b := by
      have hbase : -(1 : ℝ) ≤ 1 - (k : ℝ) / M := by linarith
      simpa [sub_eq_add_neg, mul_assoc] using
        (one_add_mul_sub_le_pow hbase b)
    calc
      ((A : ℝ) - (b : ℝ) * k) * (A : ℝ)⁻¹ ≤
          1 - (b : ℝ) * ((k : ℝ) / M) := hlinear
      _ ≤ (1 - (k : ℝ) / M) ^ b := hbern
      _ = (((M : ℝ) - k) * (M : ℝ)⁻¹) ^ b := by
        congr 1
        rw [← div_eq_mul_inv, sub_div, div_self (ne_of_gt hMreal)]
  · have hzero : A - b * k = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hbkA)
    rw [hzero]
    simp only [Nat.cast_zero, zero_mul]
    exact pow_nonneg
      (mul_nonneg (show (0 : ℝ) ≤ (M - k : ℕ) by positivity)
        (show (0 : ℝ) ≤ (M : ℝ)⁻¹ by positivity)) _

/-- The preceding inequality in exactly the arithmetic shape produced by
the three-pairs-per-triangle union estimate. -/
theorem preliminary_survival_scalar
    (A M k b : ℕ) (hA : 0 < A) (hAM : A ≤ M) (hkM : k ≤ M) :
    ((A - b * (3 * k) / 3 : ℕ) : ℝ≥0) * (A : ℝ≥0)⁻¹ ≤
      (((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^ b := by
  have hmul : b * (3 * k) = 3 * (b * k) := by ring
  rw [hmul, Nat.mul_div_cancel_left _ (by decide : 0 < 3)]
  exact nat_sub_mul_inv_le_sub_ratio_pow A M k b hA hAM hkM

end

end Erdos207
