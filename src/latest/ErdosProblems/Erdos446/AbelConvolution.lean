/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.AbelPolynomial
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Erdős Problem 446: the finite Abel convolution bound

This file turns the exact Abel-polynomial identity into the nonnegative
interior convolution used when Ford splits an ordered simplex at one
coordinate.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem abelKernel_eq_pow {x : ℝ} {n : ℕ} (hn : n ≠ 0) :
    abelKernel x n = (x + n) ^ (n - 1) := by
  simp [abelKernel, hn]

theorem abelKernel_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ abelKernel x n := by
  by_cases hn : n = 0
  · simp [abelKernel, hn, inv_nonneg.mpr hx]
  · rw [abelKernel_eq_pow hn]
    positivity

noncomputable def fordAbelInteriorSum (m : ℕ) (A B : ℝ) : ℝ :=
  ∑ j ∈ Ico 1 (m + 1),
    ((m + 1).choose j : ℝ) *
      (A + j) ^ (j - 1) *
      (B + (m + 1 - j : ℕ)) ^ (m + 1 - j - 1)

/-- The interior terms are bounded by the complete Abel convolution. -/
theorem fordAbelInteriorSum_le_complete (m : ℕ) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) :
    fordAbelInteriorSum m A B ≤
      (A⁻¹ + B⁻¹) * (A + B + (m + 1 : ℝ)) ^ m := by
  have hfull := abelKernel_convolution m hA.ne' hB.ne'
  rw [← hfull]
  calc
    fordAbelInteriorSum m A B =
        ∑ j ∈ Ico 1 (m + 1),
          ((m + 1).choose j : ℝ) * abelKernel A j *
            abelKernel B (m + 1 - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjPos : 0 < j := (Finset.mem_Ico.mp hj).1
      have hjLt : j < m + 1 := (Finset.mem_Ico.mp hj).2
      rw [abelKernel_eq_pow (Nat.ne_of_gt hjPos),
        abelKernel_eq_pow (by omega : m + 1 - j ≠ 0)]
    _ ≤ ∑ j ∈ range (m + 2),
          ((m + 1).choose j : ℝ) * abelKernel A j *
            abelKernel B (m + 1 - j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        rw [Finset.mem_range]
        have hjLt := (Finset.mem_Ico.mp hj).2
        omega
      · intro j hjRange hjNot
        exact mul_nonneg
          (mul_nonneg (by positivity) (abelKernel_nonneg hA.le j))
          (abelKernel_nonneg hB.le (m + 1 - j))

/-- Enlarging both affine bases to at least one can only increase every
interior Abel term. -/
theorem fordAbelInteriorSum_le_max (m : ℕ) {a b : ℝ}
    (ha : -1 ≤ a) (hb : 0 ≤ b) :
    fordAbelInteriorSum m a b ≤
      fordAbelInteriorSum m (max 1 a) (max 1 b) := by
  apply Finset.sum_le_sum
  intro j hj
  have hjPos : 0 < j := (Finset.mem_Ico.mp hj).1
  have hjLt : j < m + 1 := (Finset.mem_Ico.mp hj).2
  have hbaseA : 0 ≤ a + (j : ℝ) := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hjPos
    linarith
  have hbaseB : 0 ≤ b + (m + 1 - j : ℕ) := by positivity
  have hleA : a + (j : ℝ) ≤ max 1 a + (j : ℝ) := by
    gcongr
    exact le_max_right _ _
  have hleB : b + (m + 1 - j : ℕ) ≤
      max 1 b + (m + 1 - j : ℕ) := by
    gcongr
    exact le_max_right _ _
  have hchoose : 0 ≤ ((m + 1).choose j : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbaseA hleA _) hchoose)
    (pow_le_pow_left₀ hbaseB hleB _)
    (pow_nonneg hbaseB _)
    (mul_nonneg hchoose
      (pow_nonneg (by positivity : 0 ≤ max 1 a + (j : ℝ)) _))

/-- The exact positive comparison preceding Ford's numerical `e^4` bound. -/
theorem fordAbelInteriorSum_le_complete_max (m : ℕ) {a b : ℝ}
    (ha : -1 ≤ a) (hb : 0 ≤ b) :
    fordAbelInteriorSum m a b ≤
      ((max 1 a)⁻¹ + (max 1 b)⁻¹) *
        (max 1 a + max 1 b + (m + 1 : ℝ)) ^ m := by
  exact (fordAbelInteriorSum_le_max m ha hb).trans
    (fordAbelInteriorSum_le_complete m
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

/-- The elementary exponential estimate which turns an additive enlargement
of a positive base into an absolute constant. -/
theorem add_three_pow_le_exp_three_mul_pow (m : ℕ) (hm : 0 < m) {N : ℝ}
    (hmN : (m : ℝ) ≤ N) :
    (N + 3) ^ m ≤ Real.exp 3 * N ^ m := by
  have hmPos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hNPos : 0 < N := lt_of_lt_of_le hmPos hmN
  have hratio : 1 ≤ N / (m : ℝ) := by
    rw [le_div_iff₀ hmPos]
    simpa using hmN
  have hthree : 3 ≤ 3 * (N / (m : ℝ)) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hratio (show 0 ≤ (3 : ℝ) by norm_num)
  have hbase : N + 3 ≤ N * (1 + 3 / (m : ℝ)) := by
    calc
      N + 3 ≤ N + 3 * (N / (m : ℝ)) :=
        by simpa [add_comm] using add_le_add_left hthree N
      _ = N * (1 + 3 / (m : ℝ)) := by
        field_simp
  have hfactorNonneg : 0 ≤ 1 + 3 / (m : ℝ) := by positivity
  have hfactorExp : 1 + 3 / (m : ℝ) ≤
      Real.exp (3 / (m : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (3 / (m : ℝ))
  have hfactorPow : (1 + 3 / (m : ℝ)) ^ m ≤ Real.exp 3 := by
    calc
      (1 + 3 / (m : ℝ)) ^ m ≤
          (Real.exp (3 / (m : ℝ))) ^ m :=
        pow_le_pow_left₀ hfactorNonneg hfactorExp m
      _ = Real.exp ((m : ℝ) * (3 / (m : ℝ))) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp 3 := by
        congr 1
        field_simp
  calc
    (N + 3) ^ m ≤ (N * (1 + 3 / (m : ℝ))) ^ m :=
      pow_le_pow_left₀ (by positivity) hbase m
    _ = N ^ m * (1 + 3 / (m : ℝ)) ^ m := by rw [mul_pow]
    _ ≤ N ^ m * Real.exp 3 :=
      mul_le_mul_of_nonneg_left hfactorPow (pow_nonneg hNPos.le m)
    _ = Real.exp 3 * N ^ m := by ring

/-- Ford's numerical Abel-convolution bound.  The constant `exp 4` is
uniform in the length and in both admissible endpoint parameters. -/
theorem fordAbelInteriorSum_le_exp_four (m : ℕ) (hm : 0 < m) {a b : ℝ}
    (ha : -1 ≤ a) (hb : 0 ≤ b) :
    fordAbelInteriorSum m a b ≤
      Real.exp 4 * (m + 1 + a + b) ^ m := by
  let A : ℝ := max 1 a
  let B : ℝ := max 1 b
  let N : ℝ := m + 1 + a + b
  have hAOne : 1 ≤ A := le_max_left _ _
  have hBOne : 1 ≤ B := le_max_left _ _
  have hAle : A ≤ a + 2 := by
    apply max_le
    · linarith
    · linarith
  have hBle : B ≤ b + 1 := by
    apply max_le
    · linarith
    · linarith
  have hmN : (m : ℝ) ≤ N := by
    dsimp [N]
    linarith
  have hNPos : 0 < N := lt_of_lt_of_le (by exact_mod_cast hm) hmN
  have hlargeBase : A + B + (m + 1 : ℝ) ≤ N + 3 := by
    dsimp [N]
    linarith
  have hcoefficient : A⁻¹ + B⁻¹ ≤ 2 := by
    have hAInv : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hAOne
    have hBInv : B⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hBOne
    linarith
  have hlargePow : (A + B + (m + 1 : ℝ)) ^ m ≤
      Real.exp 3 * N ^ m := by
    exact (pow_le_pow_left₀ (by positivity) hlargeBase m).trans
      (add_three_pow_le_exp_three_mul_pow m hm hmN)
  have hfirst : (A⁻¹ + B⁻¹) *
      (A + B + (m + 1 : ℝ)) ^ m ≤
      2 * (Real.exp 3 * N ^ m) := by
    exact mul_le_mul hcoefficient hlargePow (pow_nonneg (by positivity) m)
      (by positivity)
  have hexp : (2 : ℝ) * Real.exp 3 ≤ Real.exp 4 := by
    calc
      (2 : ℝ) * Real.exp 3 ≤ Real.exp 1 * Real.exp 3 :=
        mul_le_mul_of_nonneg_right Real.exp_one_gt_two.le (Real.exp_nonneg _)
      _ = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  calc
    fordAbelInteriorSum m a b ≤
        (A⁻¹ + B⁻¹) * (A + B + (m + 1 : ℝ)) ^ m := by
      simpa [A, B] using fordAbelInteriorSum_le_complete_max m ha hb
    _ ≤ 2 * (Real.exp 3 * N ^ m) := hfirst
    _ = (2 * Real.exp 3) * N ^ m := by ring
    _ ≤ Real.exp 4 * N ^ m :=
      mul_le_mul_of_nonneg_right hexp (pow_nonneg hNPos.le m)
    _ = Real.exp 4 * (m + 1 + a + b) ^ m := by rfl

end Erdos446
