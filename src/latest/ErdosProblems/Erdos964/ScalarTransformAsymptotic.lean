import ErdosProblems.Erdos964.ScalarTransformEndpoint
import ErdosProblems.Erdos964.ScalarTransformRounding

/-!
# Uniform polynomial approximation of the scalar transform

The fixed-modulus density multiplies the polynomial primitive. The error
is uniform for every supported divisor below the sieve radius.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_uniform_scalar_transform_primitive_error :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧
      ∀ M R r : ℕ, 0 < M → r ∣ scalarSievePrimeProduct M R → r < R →
        2 ≤ Real.log R →
      |scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r -
        coprimeHarmonicDensity M * Real.log R *
          ggpyPolynomialPrimitive (Real.log ((R : ℝ) / r) / Real.log R)| ≤
        81 * coprimeHarmonicDensity M *
          (K + primeLogDivisorMass M + (Real.log (Real.log R) + C + 2) + Real.log 2) := by
  obtain ⟨K, C, hK, hC, hendpoint⟩ := exists_uniform_scalar_transform_endpoint_error
  refine ⟨K, C, hK, hC, ?_⟩
  intro M R r hM hr hrR hlogR
  let δ := coprimeHarmonicDensity M
  let B := K + primeLogDivisorMass M + (Real.log (Real.log R) + C + 2) + Real.log 2
  let Q := (R - 1) / r
  let V := (7 - 6 * Real.log r / Real.log R) * Real.log Q -
    (3 / Real.log R) * (Real.log Q) ^ 2
  let W := Real.log R * ggpyPolynomialPrimitive (Real.log ((R : ℝ) / r) / Real.log R)
  have hr0 := Nat.pos_of_ne_zero
    ((scalarSievePrimeProduct_squarefree M R).squarefree_of_dvd hr).ne_zero
  have hδ : 0 ≤ δ := by dsimp [δ, coprimeHarmonicDensity]; positivity
  have hmass : 0 ≤ primeLogDivisorMass M := by unfold primeLogDivisorMass; positivity
  have hloglog : 0 ≤ Real.log (Real.log R) := Real.log_nonneg (by linarith)
  have hlog2B : Real.log 2 ≤ B := by dsimp [B]; linarith
  have he : |scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r -
      δ * V| ≤ 77 * δ * B := hendpoint M R r hM hr hrR hlogR
  have hrnd : |δ * V - δ * W| ≤ 4 * δ * Real.log 2 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hδ]
    calc
      _ ≤ δ * (4 * Real.log 2) := mul_le_mul_of_nonneg_left
        (scalar_transform_primitive_rounding R r hr0 hrR) hδ
      _ = _ := by ring
  have h := (abs_sub_le
    (scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r)
    (δ * V) (δ * W)).trans (add_le_add he hrnd)
  have hfinal : |scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r -
      δ * W| ≤ 81 * δ * B := by
    refine h.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hlog2B hδ]
  simpa only [W, δ, B, mul_assoc] using hfinal

end Erdos964
