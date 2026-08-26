/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.WeightedCommonDivisorRanges
import ErdosProblems.Erdos822.CofactorCardBound

/-!
# Assembly of the weighted common-divisor average

This is the exact bookkeeping around the three genuinely arithmetic
estimates.  The unit singular part is already uniformly controlled; any
three bounds for the weighted small, medium, and large ranges therefore
give a bound for the full supported gcd kernel.
-/

namespace Erdos822

open scoped BigOperators

/-- The weighted part is the sum of its three common-divisor ranges, also
after restoring the square logarithmic sieve ratio. -/
theorem logRatio_sq_mul_sum_supportedWeighted_eq_three_ranges
    (B : Finset ℕ) (N z y : ℕ) :
    (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            supportedWeightedGcdSingularKernel (N ^ 60) m m' z y) =
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          (∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              smallWeightedCommonDivisorKernel N m m' z y) +
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          (∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              mediumWeightedCommonDivisorKernel N m m' z y) +
          (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (∑ m ∈ B,
              ∑ m' ∈ B.erase m,
                largeWeightedCommonDivisorKernel N m m' z y) := by
  rw [sum_supportedWeightedGcdSingularKernel_eq_three_ranges]
  ring

/-- If the paper's three weighted h-range sums have linear bounds, then the
full supported gcd--singular kernel has a linear bound after the square
logarithmic ratio is restored. -/
theorem exists_logRatio_sq_mul_sum_supportedGcd_le_of_threeRangeBounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ N z y : ℕ, ∀ B : Finset ℕ, ∀ Ksmall Kmedium Klarge : ℝ,
        1 ≤ N → 2 ≤ z → z ≤ y → B ⊆ oddRawCofactors N →
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (∑ m ∈ B,
              ∑ m' ∈ B.erase m,
                smallWeightedCommonDivisorKernel N m m' z y) ≤
          Ksmall * ((N ^ 60 : ℕ) : ℝ) →
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (∑ m ∈ B,
              ∑ m' ∈ B.erase m,
                mediumWeightedCommonDivisorKernel N m m' z y) ≤
          Kmedium * ((N ^ 60 : ℕ) : ℝ) →
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (∑ m ∈ B,
              ∑ m' ∈ B.erase m,
                largeWeightedCommonDivisorKernel N m m' z y) ≤
          Klarge * ((N ^ 60 : ℕ) : ℝ) →
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (∑ m ∈ B,
              ∑ m' ∈ B.erase m,
                supportedGcdSingularKernel (N ^ 60) m m' z y) ≤
          (C ^ 2 + Ksmall + Kmedium + Klarge) *
            ((N ^ 60 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hunit⟩ :=
    exists_logRatio_sq_mul_sum_supportedUnit_le_pow_fifty_six
  refine ⟨C, hC, ?_⟩
  intro N z y B Ksmall Kmedium Klarge hN hz hzy hB
    hsmall hmedium hlarge
  have hpow : N ^ 56 ≤ N ^ 60 :=
    Nat.pow_le_pow_right hN (by omega)
  have hpowCast : ((N ^ 56 : ℕ) : ℝ) ≤ ((N ^ 60 : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hunit' :
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          (∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              supportedUnitSingularKernel (N ^ 60) m m' z y) ≤
        C ^ 2 * ((N ^ 60 : ℕ) : ℝ) := by
    calc
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          (∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              supportedUnitSingularKernel (N ^ 60) m m' z y) ≤
          C ^ 2 * ((N ^ 56 : ℕ) : ℝ) := hunit N z y B hz hzy hB
      _ ≤ C ^ 2 * ((N ^ 60 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hpowCast (sq_nonneg C)
  calc
    (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
        (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            supportedGcdSingularKernel (N ^ 60) m m' z y) =
        (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (∑ m ∈ B,
              ∑ m' ∈ B.erase m,
                supportedUnitSingularKernel (N ^ 60) m m' z y) +
          (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (∑ m ∈ B,
              ∑ m' ∈ B.erase m,
                supportedWeightedGcdSingularKernel (N ^ 60) m m' z y) := by
      simp_rw [supportedGcdSingularKernel_eq_unit_add_weighted,
        Finset.sum_add_distrib]
      ring
    _ = (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
            (∑ m ∈ B,
              ∑ m' ∈ B.erase m,
                supportedUnitSingularKernel (N ^ 60) m m' z y) +
          ((Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
              (∑ m ∈ B,
                ∑ m' ∈ B.erase m,
                  smallWeightedCommonDivisorKernel N m m' z y) +
            (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
              (∑ m ∈ B,
                ∑ m' ∈ B.erase m,
                  mediumWeightedCommonDivisorKernel N m m' z y) +
              (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
                (∑ m ∈ B,
                  ∑ m' ∈ B.erase m,
                    largeWeightedCommonDivisorKernel N m m' z y)) := by
      rw [logRatio_sq_mul_sum_supportedWeighted_eq_three_ranges]
    _ ≤ C ^ 2 * ((N ^ 60 : ℕ) : ℝ) +
          (Ksmall * ((N ^ 60 : ℕ) : ℝ) +
            Kmedium * ((N ^ 60 : ℕ) : ℝ) +
              Klarge * ((N ^ 60 : ℕ) : ℝ)) := by
      linarith
    _ = (C ^ 2 + Ksmall + Kmedium + Klarge) *
          ((N ^ 60 : ℕ) : ℝ) := by ring

/-- A checked logarithmic-ratio bound for the supported gcd kernel gives a
bound for the whole supported B5 main-weight sum. -/
theorem sum_supportedSymmetricB5Weight_le_of_logRatio_kernel_bound
    {A C C₀ K : ℝ} {N z y S : ℕ} {B : Finset ℕ}
    (hA : 0 ≤ A)
    (hpos : ∀ m ∈ B, 0 < m)
    (hkernel :
      (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2 *
          (∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              supportedGcdSingularKernel (N ^ 60) m m' z y) ≤
        K * ((N ^ 60 : ℕ) : ℝ)) :
    (∑ m ∈ B,
        ∑ m' ∈ B.erase m,
          supportedSymmetricB5Weight A C C₀
            (N ^ 60) m m' z y S) ≤
      ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          (C ^ 2 * Real.exp (12 * C₀))) *
        (K * ((N ^ 60 : ℕ) : ℝ)) := by
  let R : ℝ := (Real.log (z : ℝ) / Real.log (y : ℝ)) ^ 2
  let D : ℝ :=
    (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
      (C ^ 2 * Real.exp (12 * C₀))
  have hD : 0 ≤ D := by
    dsimp [D]
    have heta : 0 ≤ 1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
      have : 0 ≤ (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
        positivity
      linarith
    exact mul_nonneg heta (mul_nonneg (sq_nonneg C) (Real.exp_pos _).le)
  have hpoint : ∀ m ∈ B, ∀ m' ∈ B.erase m,
      supportedSymmetricB5Weight A C C₀ (N ^ 60) m m' z y S ≤
        D * (R * supportedGcdSingularKernel (N ^ 60) m m' z y) := by
    intro m hm m' hm'
    have hm'B : m' ∈ B := (Finset.mem_erase.mp hm').2
    have h := supportedSymmetricB5Weight_le_factor_mul_supportedGcdKernel
      (A := A) (C := C) (C₀ := C₀) (x := N ^ 60)
      (m := m) (m' := m') (z := z) (y := y) (S := S)
      hA (hpos m hm) (hpos m' hm'B)
    calc
      supportedSymmetricB5Weight A C C₀ (N ^ 60) m m' z y S ≤
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (C ^ 2 * R * Real.exp (12 * C₀))) *
            supportedGcdSingularKernel (N ^ 60) m m' z y := by
        simpa [R] using h
      _ = D * (R * supportedGcdSingularKernel (N ^ 60) m m' z y) := by
        dsimp [D]
        ring
  calc
    (∑ m ∈ B,
        ∑ m' ∈ B.erase m,
          supportedSymmetricB5Weight A C C₀
            (N ^ 60) m m' z y S) ≤
        ∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            D * (R * supportedGcdSingularKernel (N ^ 60) m m' z y) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro m' hm'
      exact hpoint m hm m' hm'
    _ = D * (R *
          (∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              supportedGcdSingularKernel (N ^ 60) m m' z y)) := by
      simp_rw [Finset.mul_sum]
    _ ≤ D * (K * ((N ^ 60 : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [R] using hkernel
      · exact hD
    _ = ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
          (C ^ 2 * Real.exp (12 * C₀))) *
        (K * ((N ^ 60 : ℕ) : ℝ)) := by
      rfl

end Erdos822
