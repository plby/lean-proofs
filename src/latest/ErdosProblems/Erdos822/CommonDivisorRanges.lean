/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SupportedGcdKernel

/-!
# The three common-divisor ranges

At x=N^60, the GIL thresholds x^(1/20) and x^(1/3) are N^3 and N^20.
This file makes the partition literal, while retaining the support
condition that an actual outer collision exists.
-/

namespace Erdos822

open scoped BigOperators

/-- The unfiltered arithmetic expression inside the supported kernel. -/
noncomputable def gcdSingularKernelTerm
    (x m m' z y : ℕ) : ℝ :=
  (1 + ((x * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
      ((m * m' : ℕ) : ℝ)) *
    Erdos851.singularFactor (reducedTotientDet m m') z y

/-- Supported kernel in the small common-divisor range. -/
noncomputable def smallCommonDivisorKernel
    (N m m' z y : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
      shiftedCoefficientGcd m m' ≤ N ^ 3 then
    gcdSingularKernelTerm (N ^ 60) m m' z y
  else 0

/-- Supported kernel in the medium common-divisor range. -/
noncomputable def mediumCommonDivisorKernel
    (N m m' z y : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
      N ^ 3 < shiftedCoefficientGcd m m' ∧
      shiftedCoefficientGcd m m' ≤ N ^ 20 then
    gcdSingularKernelTerm (N ^ 60) m m' z y
  else 0

/-- Supported kernel in the large common-divisor range. -/
noncomputable def largeCommonDivisorKernel
    (N m m' z y : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
      N ^ 20 < shiftedCoefficientGcd m m' then
    gcdSingularKernelTerm (N ^ 60) m m' z y
  else 0

theorem supportedGcdSingularKernel_eq_three_ranges
    (N m m' z y : ℕ) :
    supportedGcdSingularKernel (N ^ 60) m m' z y =
      smallCommonDivisorKernel N m m' z y +
        mediumCommonDivisorKernel N m m' z y +
          largeCommonDivisorKernel N m m' z y := by
  unfold supportedGcdSingularKernel smallCommonDivisorKernel
    mediumCommonDivisorKernel largeCommonDivisorKernel
    gcdSingularKernelTerm
  by_cases hne : (outerCollisionPairs (N ^ 60) m m').Nonempty
  · rw [if_pos hne]
    by_cases hsmall : shiftedCoefficientGcd m m' ≤ N ^ 3
    · have hpow : N ^ 3 ≤ N ^ 20 := by
        by_cases hN : N = 0
        · simp [hN]
        · exact Nat.pow_le_pow_right
            (Nat.one_le_iff_ne_zero.mpr hN) (by omega)
      have hnotLarge :
          ¬ N ^ 20 < shiftedCoefficientGcd m m' :=
        not_lt_of_ge (hsmall.trans hpow)
      simp [hne, hsmall, not_lt_of_ge hsmall, hnotLarge]
    · have hsmall' : N ^ 3 < shiftedCoefficientGcd m m' := by omega
      by_cases hmedium : shiftedCoefficientGcd m m' ≤ N ^ 20
      · simp [hne, hsmall, hsmall', hmedium]
      · have hlarge : N ^ 20 < shiftedCoefficientGcd m m' := by omega
        simp [hne, hsmall, hsmall', hmedium, hlarge]
  · simp [hne]

/-- The double supported-kernel sum splits exactly into the three GIL
common-divisor ranges. -/
theorem sum_supportedGcdSingularKernel_eq_three_ranges
    (B : Finset ℕ) (N z y : ℕ) :
    (∑ m ∈ B,
        ∑ m' ∈ B.erase m,
          supportedGcdSingularKernel (N ^ 60) m m' z y) =
      (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            smallCommonDivisorKernel N m m' z y) +
        (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            mediumCommonDivisorKernel N m m' z y) +
          ∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              largeCommonDivisorKernel N m m' z y := by
  simp_rw [supportedGcdSingularKernel_eq_three_ranges,
    Finset.sum_add_distrib]

theorem smallCommonDivisorKernel_nonneg
    (N m m' z y : ℕ) :
    0 ≤ smallCommonDivisorKernel N m m' z y := by
  unfold smallCommonDivisorKernel gcdSingularKernelTerm
  split_ifs
  · exact mul_nonneg (by positivity) (singularFactor_nonneg _ _ _)
  · exact le_rfl

theorem mediumCommonDivisorKernel_nonneg
    (N m m' z y : ℕ) :
    0 ≤ mediumCommonDivisorKernel N m m' z y := by
  unfold mediumCommonDivisorKernel gcdSingularKernelTerm
  split_ifs
  · exact mul_nonneg (by positivity) (singularFactor_nonneg _ _ _)
  · exact le_rfl

theorem largeCommonDivisorKernel_nonneg
    (N m m' z y : ℕ) :
    0 ≤ largeCommonDivisorKernel N m m' z y := by
  unfold largeCommonDivisorKernel gcdSingularKernelTerm
  split_ifs
  · exact mul_nonneg (by positivity) (singularFactor_nonneg _ _ _)
  · exact le_rfl

end Erdos822
