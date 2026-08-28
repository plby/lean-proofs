import Wikipedia.NoExoticSixSphere.OrthogonalIndexTestField
import Wikipedia.NoExoticSixSphere.OrthogonalExponentialVariation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# An explicit negative-direction criterion for orthogonal path energy

The fixed-endpoint rotating sine field has index form
`π² ‖A‖²_HS - ‖[K,A]‖²_HS / 4`. This is also the actual second energy
derivative of its exponential variation. A sufficiently large commutator
therefore gives an actual negative direction, not merely a formal quadratic
expression.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalIndexTestField

open GLOrthonormalization CayleyTransform HilbertSchmidt OrthogonalCommutator
  OrthogonalIndexForm OrthogonalExponential

variable {n : ℕ}

theorem integral_sin_pi_sq :
    (∫ t : ℝ in 0..1, Real.sin (Real.pi * t) ^ 2) = 1 / 2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ ↦ Real.sin t ^ 2) Real.pi_ne_zero]
  simp only [mul_zero, mul_one, integral_sin_sq, Real.sin_zero,
    Real.cos_zero, Real.sin_pi, Real.cos_pi, zero_mul, sub_zero, zero_add, smul_eq_mul]
  field_simp

theorem integral_cos_pi_sq :
    (∫ t : ℝ in 0..1, Real.cos (Real.pi * t) ^ 2) = 1 / 2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ ↦ Real.cos t ^ 2) Real.pi_ne_zero]
  simp only [mul_zero, mul_one, integral_cos_sq, Real.sin_zero,
    Real.cos_zero, Real.sin_pi, Real.cos_pi, mul_zero, sub_zero, zero_add, smul_eq_mul]
  field_simp

theorem integral_density_field (K A : SkewOperators n) :
    (2 * ∫ t : ℝ in 0..1, density K (field K A t : Vector n →L[ℝ] Vector n)
      ((deriv (field K A) t : SkewOperators n) : Vector n →L[ℝ] Vector n)) =
        Real.pi ^ 2 * squareNorm (A : Vector n →L[ℝ] Vector n) -
          (1 / 4 : ℝ) * squareNorm (commutator (K : Vector n →L[ℝ] Vector n)
            (A : Vector n →L[ℝ] Vector n)) := by
  have hcos : Continuous (fun t : ℝ ↦
      Real.pi ^ 2 * Real.cos (Real.pi * t) ^ 2 * squareNorm (A : Vector n →L[ℝ] Vector n)) := by
    fun_prop
  have hsin : Continuous (fun t : ℝ ↦
      (1 / 4 : ℝ) * Real.sin (Real.pi * t) ^ 2 *
        squareNorm (commutator (K : Vector n →L[ℝ] Vector n)
          (A : Vector n →L[ℝ] Vector n))) := by
    fun_prop
  simp_rw [density_field]
  rw [intervalIntegral.integral_sub (hcos.intervalIntegrable 0 1) (hsin.intervalIntegrable 0 1)]
  simp only [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    integral_cos_pi_sq, integral_sin_pi_sq]
  ring

/-- The explicit quadratic value is the second derivative of an actual fixed-endpoint variation. -/
theorem hasDerivAt_deriv_energy_testField (b : OrthogonalOperators n) (K A : SkewOperators n) :
    HasDerivAt (deriv (fun s ↦ OrthogonalPathEnergy.energy
      (fun t ↦ (OrthogonalExponentialVariation.family
        (fun r ↦ b * exp (r • K)) (field K A) (s, t)).1.1) 0 1))
      (Real.pi ^ 2 * squareNorm (A : Vector n →L[ℝ] Vector n) -
        (1 / 4 : ℝ) * squareNorm (commutator (K : Vector n →L[ℝ] Vector n)
          (A : Vector n →L[ℝ] Vector n))) 0 := by
  have hγ : ContDiff ℝ ∞ (fun t : ℝ ↦ (b * exp (t • K)).1.1) :=
    contDiff_const.clm_comp (SkewConjugation.contDiff_exp_smul_operator K)
  have hd := OrthogonalExponentialVariation.hasDerivAt_deriv_energy_family hγ
    (contDiff_field K A) 0 1 (field_zero K A) (field_one K A) b K (fun _ ↦ rfl)
  rw [integral_density_field] at hd
  exact hd

theorem negative_index_of_commutator (K A : SkewOperators n)
    (h : 4 * Real.pi ^ 2 * squareNorm (A : Vector n →L[ℝ] Vector n) <
      squareNorm (commutator (K : Vector n →L[ℝ] Vector n)
        (A : Vector n →L[ℝ] Vector n))) :
    (2 * ∫ t : ℝ in 0..1, density K (field K A t : Vector n →L[ℝ] Vector n)
      ((deriv (field K A) t : SkewOperators n) : Vector n →L[ℝ] Vector n)) < 0 := by
  rw [integral_density_field]
  linarith

/-- Under the commutator bound, the constructed family's actual second energy
derivative is negative. -/
theorem negative_secondDerivative (b : OrthogonalOperators n) (K A : SkewOperators n)
    (h : 4 * Real.pi ^ 2 * squareNorm (A : Vector n →L[ℝ] Vector n) <
      squareNorm (commutator (K : Vector n →L[ℝ] Vector n)
        (A : Vector n →L[ℝ] Vector n))) :
    deriv (deriv (fun s ↦ OrthogonalPathEnergy.energy
      (fun t ↦ (OrthogonalExponentialVariation.family
        (fun r ↦ b * exp (r • K)) (field K A) (s, t)).1.1) 0 1)) 0 < 0 := by
  rw [(hasDerivAt_deriv_energy_testField b K A).deriv]
  linarith

end NoExoticSixSphere.OrthogonalIndexTestField
