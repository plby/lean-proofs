import ErdosProblems.Erdos964.ScalarTransformPolynomial
import ErdosProblems.Erdos964.SquaredDifferenceError

/-!
# Uniform approximation of the squared transformed difference
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_uniform_scalar_transform_difference_sq_error :
    ∃ K C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ M R r s : ℕ,
      0 < M → 2 ≤ Real.log R → Squarefree r → r.Coprime M →
      Squarefree s → s.Coprime M →
      |(scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r -
          scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) s) ^ 2 -
        (coprimeHarmonicDensity M *
          (scalarTransformPolynomial R r - scalarTransformPolynomial R s)) ^ 2| ≤
        (2 * scalarTransformErrorEnvelope M R K C) *
          (2 * scalarTransformErrorEnvelope M R K C +
            16 * (coprimeHarmonicDensity M * Real.log R)) := by
  obtain ⟨K, C, hK, hC, hbound⟩ := exists_uniform_scalar_transform_polynomial_error
  refine ⟨K, C, hK, hC, ?_⟩
  intro M R r s hM hR hrsq hrM hssq hsM
  let δ := coprimeHarmonicDensity M
  let E := scalarTransformErrorEnvelope M R K C
  have hδ : 0 ≤ δ := by dsimp [δ, coprimeHarmonicDensity]; positivity
  have hE : 0 ≤ E := scalarTransformErrorEnvelope_nonneg M R K C hK.le hC hR
  have hpoly (u : ℕ) : |δ * scalarTransformPolynomial R u| ≤ 4 * (δ * Real.log R) := by
    have hu := scalarTransformPolynomial_bounds R u (by linarith)
    rw [abs_mul, abs_of_nonneg hδ, abs_of_nonneg hu.1]
    calc
      _ ≤ δ * (4 * Real.log R) := mul_le_mul_of_nonneg_left hu.2 hδ
      _ = _ := by ring
  have h := abs_difference_sq_error
    (scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r)
    (scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) s)
    (δ * scalarTransformPolynomial R r) (δ * scalarTransformPolynomial R s)
    E (δ * Real.log R) hE (hbound M R r hM hR hrsq hrM)
      (hbound M R s hM hR hssq hsM) (hpoly r) (hpoly s)
  rw [← mul_sub] at h
  exact h

end Erdos964
