/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.KernelSplit

/-!
# Removing the determinant singular factor from the global average

After restoring the square logarithmic ratio from the two-prime sieve, the
determinant singular factor is bounded pointwise by an absolute constant.
Consequently the genuinely arithmetic task is exactly the supported average
of `N^60 * gcd(m+φ(m),m'+φ(m')) / (m*m')`.
-/

namespace Erdos822

open scoped BigOperators

/-- The supported gcd-over-product scale with no singular factor. -/
noncomputable def supportedGcdScale (N m m' : ℕ) : ℝ :=
  if (outerCollisionPairs (N ^ 60) m m').Nonempty then
    ((N ^ 60 * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
      ((m * m' : ℕ) : ℝ)
  else 0

theorem supportedGcdScale_nonneg (N m m' : ℕ) :
    0 ≤ supportedGcdScale N m m' := by
  unfold supportedGcdScale
  split_ifs <;> positivity

/-- Pointwise removal of the singular factor after the log-ratio square is
restored. -/
theorem exists_logRatio_sq_mul_supportedWeighted_le_gcdScale :
    ∃ C : ℝ, 0 < C ∧
      ∀ N m m' z y : ℕ, 2 ≤ z → z ≤ y →
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            supportedWeightedGcdSingularKernel
              (N ^ 60) m m' z y ≤
          C ^ 2 * supportedGcdScale N m m' := by
  obtain ⟨C, hC, hsing⟩ := exists_logRatio_sq_mul_singularFactor_upper
  refine ⟨C, hC, ?_⟩
  intro N m m' z y hz hzy
  unfold supportedWeightedGcdSingularKernel supportedGcdScale
  by_cases hne : (outerCollisionPairs (N ^ 60) m m').Nonempty
  · rw [if_pos hne, if_pos hne]
    let X : ℝ :=
      ((N ^ 60 * shiftedCoefficientGcd m m' : ℕ) : ℝ) /
        ((m * m' : ℕ) : ℝ)
    have hX : 0 ≤ X := by
      dsimp [X]
      positivity
    calc
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          (X * Erdos851.singularFactor
            (reducedTotientDet m m') z y) =
        X * ((Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          Erdos851.singularFactor
            (reducedTotientDet m m') z y) := by ring
      _ ≤ X * C ^ 2 :=
        mul_le_mul_of_nonneg_left
          (hsing (reducedTotientDet m m') z y hz hzy) hX
      _ = C ^ 2 * X := by ring
  · simp [hne]

/-- Summed form of the pointwise singular-factor removal. -/
theorem exists_logRatio_sq_mul_sum_supportedWeighted_le_sum_gcdScale :
    ∃ C : ℝ, 0 < C ∧
      ∀ N z y : ℕ, ∀ B : Finset ℕ, 2 ≤ z → z ≤ y →
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (∑ m ∈ B,
              ∑ m' ∈ B.erase m,
                supportedWeightedGcdSingularKernel
                  (N ^ 60) m m' z y) ≤
          C ^ 2 *
            (∑ m ∈ B,
              ∑ m' ∈ B.erase m,
                supportedGcdScale N m m') := by
  obtain ⟨C, hC, hpoint⟩ :=
    exists_logRatio_sq_mul_supportedWeighted_le_gcdScale
  refine ⟨C, hC, ?_⟩
  intro N z y B hz hzy
  calc
    (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            supportedWeightedGcdSingularKernel
              (N ^ 60) m m' z y) =
      ∑ m ∈ B,
        ∑ m' ∈ B.erase m,
          (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            supportedWeightedGcdSingularKernel
              (N ^ 60) m m' z y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ B,
        ∑ m' ∈ B.erase m,
          C ^ 2 * supportedGcdScale N m m' := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro m' hm'
      exact hpoint N m m' z y hz hzy
    _ = C ^ 2 *
        (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            supportedGcdScale N m m') := by
      simp_rw [Finset.mul_sum]

/-- A linear supported gcd-scale average supplies the weighted-kernel bound
needed by the B5 energy assembly. -/
theorem exists_logRatio_sq_mul_sum_supportedWeighted_le_of_gcdScale_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ N z y : ℕ, ∀ B : Finset ℕ, ∀ K : ℝ,
        2 ≤ z → z ≤ y →
        (∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              supportedGcdScale N m m') ≤
          K * ((N ^ 60 : ℕ) : ℝ) →
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (∑ m ∈ B,
              ∑ m' ∈ B.erase m,
                supportedWeightedGcdSingularKernel
                  (N ^ 60) m m' z y) ≤
          (C ^ 2 * K) * ((N ^ 60 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hsum⟩ :=
    exists_logRatio_sq_mul_sum_supportedWeighted_le_sum_gcdScale
  refine ⟨C, hC, ?_⟩
  intro N z y B K hz hzy hgcd
  calc
    (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            supportedWeightedGcdSingularKernel
              (N ^ 60) m m' z y) ≤
      C ^ 2 *
        (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            supportedGcdScale N m m') := hsum N z y B hz hzy
    _ ≤ C ^ 2 * (K * ((N ^ 60 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hgcd (sq_nonneg C)
    _ = (C ^ 2 * K) * ((N ^ 60 : ℕ) : ℝ) := by ring

end Erdos822
