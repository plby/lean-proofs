/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CofactorCardBound

/-!
# Splitting the supported kernel

The additive one in the sorted scale is harmless: after multiplication by
the square logarithmic sieve ratio, its singular factor is uniformly
bounded and there are only N^56 cofactor pairs.  The remaining term is the
genuinely arithmetic gcd-weighted average.
-/

namespace Erdos822

open scoped BigOperators

/-- Supported determinant singular factor without the gcd scale. -/
noncomputable def supportedUnitSingularKernel
    (x m m' z y : ℕ) : ℝ :=
  if (outerCollisionPairs x m m').Nonempty then
    Erdos851.singularFactor (reducedTotientDet m m') z y
  else 0

/-- Supported gcd-over-product part of the arithmetic kernel. -/
noncomputable def supportedWeightedGcdSingularKernel
    (x m m' z y : ℕ) : ℝ :=
  if (outerCollisionPairs x m m').Nonempty then
    (((x * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
        ((m * m' : ℕ) : ℝ)) *
      Erdos851.singularFactor (reducedTotientDet m m') z y
  else 0

theorem supportedGcdSingularKernel_eq_unit_add_weighted
    (x m m' z y : ℕ) :
    supportedGcdSingularKernel x m m' z y =
      supportedUnitSingularKernel x m m' z y +
        supportedWeightedGcdSingularKernel x m m' z y := by
  unfold supportedGcdSingularKernel supportedUnitSingularKernel
    supportedWeightedGcdSingularKernel
  by_cases hne : (outerCollisionPairs x m m').Nonempty
  · rw [if_pos hne, if_pos hne, if_pos hne]
    ring
  · simp [hne]

theorem supportedUnitSingularKernel_nonneg
    (x m m' z y : ℕ) :
    0 ≤ supportedUnitSingularKernel x m m' z y := by
  unfold supportedUnitSingularKernel
  split_ifs
  · exact singularFactor_nonneg _ _ _
  · exact le_rfl

theorem supportedWeightedGcdSingularKernel_nonneg
    (x m m' z y : ℕ) :
    0 ≤ supportedWeightedGcdSingularKernel x m m' z y := by
  unfold supportedWeightedGcdSingularKernel
  split_ifs
  · exact mul_nonneg (by positivity) (singularFactor_nonneg _ _ _)
  · exact le_rfl

/-- The square logarithmic ratio times the singular factor is uniformly
bounded, before any averaging. -/
theorem exists_logRatio_sq_mul_singularFactor_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ h z y : ℕ, 2 ≤ z → z ≤ y →
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          Erdos851.singularFactor h z y ≤ C ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_logRatio_sq_mul_exp_divisorMass_upper
  refine ⟨C, hC, ?_⟩
  intro h z y hz hzy
  have hratio0 :
      0 ≤ (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 :=
    sq_nonneg _
  calc
    (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        Erdos851.singularFactor h z y ≤
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          Real.exp (2 * divisorReciprocalMass h z y) :=
      mul_le_mul_of_nonneg_left
        (singularFactor_le_exp_divisorReciprocalMass h z y hz)
        hratio0
    _ ≤ C ^ 2 := hbound h z y hz hzy

/-- Consequently the unit part of the supported kernel costs at most a
fixed constant times N^56 after the square sieve ratio is restored. -/
theorem exists_logRatio_sq_mul_sum_supportedUnit_le_pow_fifty_six :
    ∃ C : ℝ, 0 < C ∧
      ∀ N z y : ℕ, ∀ B : Finset ℕ,
        2 ≤ z → z ≤ y → B ⊆ oddRawCofactors N →
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          (∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              supportedUnitSingularKernel (N ^ 60) m m' z y) ≤
          C ^ 2 * ((N ^ 56 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_logRatio_sq_mul_singularFactor_upper
  refine ⟨C, hC, ?_⟩
  intro N z y B hz hzy hB
  have hterm : ∀ m ∈ B, ∀ m' ∈ B.erase m,
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          supportedUnitSingularKernel (N ^ 60) m m' z y ≤ C ^ 2 := by
    intro m hm m' hm'
    unfold supportedUnitSingularKernel
    by_cases hne : (outerCollisionPairs (N ^ 60) m m').Nonempty
    · rw [if_pos hne]
      exact hpoint (reducedTotientDet m m') z y hz hzy
    · rw [if_neg hne]
      simpa using sq_nonneg C
  calc
    (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            supportedUnitSingularKernel (N ^ 60) m m' z y) =
        ∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
              supportedUnitSingularKernel (N ^ 60) m m' z y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ B, ∑ m' ∈ B.erase m, C ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro m' hm'
      exact hterm m hm m' hm'
    _ ≤ C ^ 2 * ((N ^ 56 : ℕ) : ℝ) :=
      sum_const_offDiagonal_le_pow_fifty_six_of_subset_oddRaw
        hB (sq_nonneg C)

end Erdos822
