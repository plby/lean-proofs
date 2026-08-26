/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierNormalizedEndpoint

/-!
# Exponential--polynomial envelope for the source coefficient mass

The natural ceilings in the two product radii cost only fixed factors.
Their logarithmic powers remain polynomial in the ambient log scale.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem ceil_exp_le_two_mul_exp {t : ℝ} (ht : 0 ≤ t) :
    (⌈Real.exp t⌉₊ : ℝ) ≤ 2 * Real.exp t := by
  have hceil := (Nat.ceil_lt_add_one (Real.exp_pos t).le).le
  have hexp : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  linarith

theorem log_ceil_exp_le_add_one {t : ℝ} (ht : 0 ≤ t) :
    Real.log (⌈Real.exp t⌉₊ : ℝ) ≤ t + 1 := by
  have hpos : (0 : ℝ) < ⌈Real.exp t⌉₊ :=
    (Real.exp_pos t).trans_le (Nat.le_ceil _)
  have hlog := Real.log_le_log hpos (ceil_exp_le_two_mul_exp ht)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  linarith

theorem one_add_log_ceil_exp_nonneg (t : ℝ) :
    0 ≤ 1 + Real.log (⌈Real.exp t⌉₊ : ℝ) := by
  have hnat : 0 < ⌈Real.exp t⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos t)
  have hlog := Real.log_nonneg (by exact_mod_cast hnat : (1 : ℝ) ≤ ⌈Real.exp t⌉₊)
  linarith

theorem sourceSelbergProductMassBound_le_exp_poly
    (K : ℕ) {C A LD LE V : ℝ} (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hAone : A ≤ 1) (hD : 0 ≤ LD) (hE : 0 ≤ LE)
    (hDV : LD ≤ V) (hEV : LE ≤ V) (hV : 0 ≤ V) :
    sourceSelbergProductMassBound K C A LD LE ≤
      4 * C * ((K : ℝ) + 2) ^ (2 * K) * (V + 1) ^ (2 * K) *
        Real.exp (A * LD + (K : ℝ) * LE) := by
  have htD : 0 ≤ A * LD := mul_nonneg hA hD
  have htE : 0 ≤ (K : ℝ) * LE := mul_nonneg (Nat.cast_nonneg _) hE
  have htDV : A * LD ≤ V := (mul_le_mul_of_nonneg_right hAone hD).trans (by simpa using hDV)
  have hbaseD : 1 + Real.log (⌈Real.exp (A * LD)⌉₊ : ℝ) ≤ ((K : ℝ) + 2) * (V + 1) := by
    have hlog := log_ceil_exp_le_add_one htD
    have hkV := mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K) hV
    nlinarith
  have hbaseE : 1 + Real.log (⌈Real.exp ((K : ℝ) * LE)⌉₊ : ℝ) ≤
      ((K : ℝ) + 2) * (V + 1) := by
    have hlog := log_ceil_exp_le_add_one htE
    have hKLE := mul_le_mul_of_nonneg_left hEV (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    nlinarith
  have hDfactor : (⌈Real.exp (A * LD)⌉₊ : ℝ) *
      (1 + Real.log (⌈Real.exp (A * LD)⌉₊ : ℝ)) ^ K ≤
      (2 * Real.exp (A * LD)) * (((K : ℝ) + 2) * (V + 1)) ^ K :=
    mul_le_mul (ceil_exp_le_two_mul_exp htD)
      (pow_le_pow_left₀ (one_add_log_ceil_exp_nonneg _) hbaseD K)
      (pow_nonneg (one_add_log_ceil_exp_nonneg _) K) (by positivity)
  have hEfactor : (⌈Real.exp ((K : ℝ) * LE)⌉₊ : ℝ) *
      (1 + Real.log (⌈Real.exp ((K : ℝ) * LE)⌉₊ : ℝ)) ^ K ≤
      (2 * Real.exp ((K : ℝ) * LE)) * (((K : ℝ) + 2) * (V + 1)) ^ K :=
    mul_le_mul (ceil_exp_le_two_mul_exp htE)
      (pow_le_pow_left₀ (one_add_log_ceil_exp_nonneg _) hbaseE K)
      (pow_nonneg (one_add_log_ceil_exp_nonneg _) K) (by positivity)
  unfold sourceSelbergProductMassBound
  calc
    _ ≤ C * ((2 * Real.exp (A * LD)) * (((K : ℝ) + 2) * (V + 1)) ^ K) *
        ((2 * Real.exp ((K : ℝ) * LE)) * (((K : ℝ) + 2) * (V + 1)) ^ K) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hDfactor hC) hEfactor
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (one_add_log_ceil_exp_nonneg _) K))
        (by positivity)
    _ = _ := by
      rw [Real.exp_add]
      simp only [two_mul, pow_add, mul_pow]
      ring

end

end Erdos4b
