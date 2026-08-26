/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.KernelSplit

/-!
# Three ranges for the weighted supported kernel

The paper's common-divisor average is applied to the term carrying the
factor `x * gcd / (m*m')`.  The additive unit in the symmetric scale has
already been separated in `KernelSplit`; this file partitions only the
remaining weighted term at the literal `N^3` and `N^20` thresholds.
-/

namespace Erdos822

open scoped BigOperators

/-- Supported gcd-weighted singular kernel in the small common-divisor
range. -/
noncomputable def smallWeightedCommonDivisorKernel
    (N m m' z y : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
      shiftedCoefficientGcd m m' ≤ N ^ 3 then
    (((N ^ 60 * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
        ((m * m' : ℕ) : ℝ)) *
      Erdos851.singularFactor (reducedTotientDet m m') z y
  else 0

/-- Supported gcd-weighted singular kernel in the medium common-divisor
range. -/
noncomputable def mediumWeightedCommonDivisorKernel
    (N m m' z y : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
      N ^ 3 < shiftedCoefficientGcd m m' ∧
      shiftedCoefficientGcd m m' ≤ N ^ 20 then
    (((N ^ 60 * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
        ((m * m' : ℕ) : ℝ)) *
      Erdos851.singularFactor (reducedTotientDet m m') z y
  else 0

/-- Supported gcd-weighted singular kernel in the large common-divisor
range. -/
noncomputable def largeWeightedCommonDivisorKernel
    (N m m' z y : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
      N ^ 20 < shiftedCoefficientGcd m m' then
    (((N ^ 60 * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
        ((m * m' : ℕ) : ℝ)) *
      Erdos851.singularFactor (reducedTotientDet m m') z y
  else 0

theorem supportedWeightedGcdSingularKernel_eq_three_ranges
    (N m m' z y : ℕ) :
    supportedWeightedGcdSingularKernel (N ^ 60) m m' z y =
      smallWeightedCommonDivisorKernel N m m' z y +
        mediumWeightedCommonDivisorKernel N m m' z y +
          largeWeightedCommonDivisorKernel N m m' z y := by
  unfold supportedWeightedGcdSingularKernel
    smallWeightedCommonDivisorKernel mediumWeightedCommonDivisorKernel
    largeWeightedCommonDivisorKernel
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

theorem sum_supportedWeightedGcdSingularKernel_eq_three_ranges
    (B : Finset ℕ) (N z y : ℕ) :
    (∑ m ∈ B,
        ∑ m' ∈ B.erase m,
          supportedWeightedGcdSingularKernel (N ^ 60) m m' z y) =
      (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            smallWeightedCommonDivisorKernel N m m' z y) +
        (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            mediumWeightedCommonDivisorKernel N m m' z y) +
          ∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              largeWeightedCommonDivisorKernel N m m' z y := by
  simp_rw [supportedWeightedGcdSingularKernel_eq_three_ranges,
    Finset.sum_add_distrib]

theorem smallWeightedCommonDivisorKernel_nonneg
    (N m m' z y : ℕ) :
    0 ≤ smallWeightedCommonDivisorKernel N m m' z y := by
  unfold smallWeightedCommonDivisorKernel
  split_ifs
  · exact mul_nonneg (by positivity) (singularFactor_nonneg _ _ _)
  · exact le_rfl

theorem mediumWeightedCommonDivisorKernel_nonneg
    (N m m' z y : ℕ) :
    0 ≤ mediumWeightedCommonDivisorKernel N m m' z y := by
  unfold mediumWeightedCommonDivisorKernel
  split_ifs
  · exact mul_nonneg (by positivity) (singularFactor_nonneg _ _ _)
  · exact le_rfl

theorem largeWeightedCommonDivisorKernel_nonneg
    (N m m' z y : ℕ) :
    0 ≤ largeWeightedCommonDivisorKernel N m m' z y := by
  unfold largeWeightedCommonDivisorKernel
  split_ifs
  · exact mul_nonneg (by positivity) (singularFactor_nonneg _ _ _)
  · exact le_rfl

end Erdos822
