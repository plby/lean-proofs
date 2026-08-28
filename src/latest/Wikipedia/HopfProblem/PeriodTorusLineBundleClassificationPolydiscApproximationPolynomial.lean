import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticBasic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Explicit finite Cauchy polynomials

The coefficients are values of the actual normalized double-circle integral
on fixed continuous boundary functions.  Each approximant is literally a
finite double sum of complex monomials, so it is entire analytic.  No
polynomial approximation theorem is used in its construction.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation

open CuspNormalization.Germs.NormalIntegral
open PeriodTorusLineBundleClassificationPolydiscAnalytic

theorem boundaryFirst_norm (R : ℝ) (w : BoundaryTorus R R) :
    ‖boundaryFirst R R w‖ = R := by
  simpa only [boundaryFirst, ContinuousMap.coe_mk, mem_sphere, dist_zero_right] using w.1.2

theorem boundarySecond_norm (R : ℝ) (w : BoundaryTorus R R) :
    ‖boundarySecond R R w‖ = R := by
  simpa only [boundarySecond, ContinuousMap.coe_mk, mem_sphere, dist_zero_right] using w.2.2

theorem boundaryFirst_ne_zero {R : ℝ} (hR : 0 < R) (w : BoundaryTorus R R) :
    boundaryFirst R R w ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [boundaryFirst_norm]
  exact hR.ne'

theorem boundarySecond_ne_zero {R : ℝ} (hR : 0 < R) (w : BoundaryTorus R R) :
    boundarySecond R R w ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [boundarySecond_norm]
  exact hR.ne'

/-- The actual boundary function whose double contour integral is the
coefficient of the monomial with exponents `(i,j)`. -/
def coefficientBoundary (R : ℝ) (u : C(BoundaryTorus R R, ℂ)) (i j : ℕ) :
    C(BoundaryTorus R R, ℂ) :=
  Ring.inverse (boundaryFirst R R) ^ (i + 1) *
    Ring.inverse (boundarySecond R R) ^ (j + 1) * u

theorem coefficientBoundary_apply {R : ℝ} (hR : 0 < R)
    (u : C(BoundaryTorus R R, ℂ)) (i j : ℕ) (w : BoundaryTorus R R) :
    coefficientBoundary R u i j w =
      (w.1.1 : ℂ)⁻¹ ^ (i + 1) * (w.2.1 : ℂ)⁻¹ ^ (j + 1) * u w := by
  simp only [coefficientBoundary, ContinuousMap.mul_apply, ContinuousMap.pow_apply]
  rw [inverse_continuousMap_apply _ (boundaryFirst_ne_zero hR),
    inverse_continuousMap_apply _ (boundarySecond_ne_zero hR)]
  rfl

/-- Finite geometric kernels, expressed directly as a finite sum of
monomials with fixed continuous boundary coefficients. -/
def partialBoundaryKernel (R : ℝ) (u : C(BoundaryTorus R R, ℂ))
    (N : ℕ) (z : ℂ × ℂ) : C(BoundaryTorus R R, ℂ) :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    (z.1 ^ i * z.2 ^ j) • coefficientBoundary R u i j

/-- The coefficients are actual contour-integral values. -/
def cauchyCoefficient (R : ℝ) (hR : 0 < R)
    (u : C(BoundaryTorus R R, ℂ)) (i j : ℕ) : ℂ :=
  normalizedDoubleCircleIntegralCLM R hR R hR (coefficientBoundary R u i j)

/-- The explicit entire polynomial, with only finitely many terms. -/
def cauchyPolynomial (R : ℝ) (hR : 0 < R)
    (u : C(BoundaryTorus R R, ℂ)) (N : ℕ) (z : ℂ × ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    cauchyCoefficient R hR u i j * z.1 ^ i * z.2 ^ j

theorem cauchyPolynomial_eq_functional (R : ℝ) (hR : 0 < R)
    (u : C(BoundaryTorus R R, ℂ)) (N : ℕ) (z : ℂ × ℂ) :
    cauchyPolynomial R hR u N z =
      normalizedDoubleCircleIntegralCLM R hR R hR (partialBoundaryKernel R u N z) := by
  simp only [cauchyPolynomial, partialBoundaryKernel, map_sum, map_smul,
    smul_eq_mul, cauchyCoefficient]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The finite formula has genuine global `ω` regularity. -/
theorem cauchyPolynomial_contDiff (R : ℝ) (hR : 0 < R)
    (u : C(BoundaryTorus R R, ℂ)) (N : ℕ) :
    ContDiff ℂ ω (cauchyPolynomial R hR u N) := by
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact (contDiff_const.mul (contDiff_fst.pow i)).mul (contDiff_snd.pow j)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation
