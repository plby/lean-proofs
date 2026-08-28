import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspExponential
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalAlternating
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# The actual canonical-volume pullback of the reference cusp exponential

The reference rays give logarithmic coordinates `(s - ζ₀ - ζ₁, ζ₀, ζ₁)`.
We evaluate the genuine derivative on the base-first basis of `ℂ × ℂ²`.
The resulting matrix has positive determinant
`(2πi)³ exp(2πis)`, and hence gives the corresponding equality of continuous
alternating three-covectors.  In particular, no formal determinant or
orientation convention is substituted for pullback of the native toric volume.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback

open CuspUniformization HolomorphicForms.Cusp

/-- The genuine derivative on the ordered base-first product basis. -/
theorem referenceExponential_derivative_matrix (p : LogModel) :
    Matrix.of (fun i => refExpDerivative p (TrianglePeriodFamily.Canonical.basis i)) =
      !![(2 * Real.pi * Complex.I : ℂ) * refExp p 0, 0, 0;
        -((2 * Real.pi * Complex.I : ℂ) * refExp p 0),
          (2 * Real.pi * Complex.I : ℂ) * refExp p 1, 0;
        -((2 * Real.pi * Complex.I : ℂ) * refExp p 0), 0,
          (2 * Real.pi * Complex.I : ℂ) * refExp p 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TrianglePeriodFamily.Canonical.basis, refExpDerivative_apply,
      Pi.basisFun_apply, smul_eq_mul]

/-- The product of the three actual chart coordinates is the cusp parameter. -/
theorem referenceExponential_product (p : LogModel) :
    refExp p 0 * refExp p 1 * refExp p 2 = exponential p.1 := by
  change exponential (p.1 - p.2 0 - p.2 1) * exponential (p.2 0) *
    exponential (p.2 1) = exponential p.1
  rw [← exponential_add, ← exponential_add]
  congr 1
  ring

/-- Coefficient of the actual derivative pullback, evaluated on the genuine basis. -/
theorem referenceExponential_derivative_volume_coefficient (p : LogModel) :
    TrianglePeriodFamily.Canonical.coefficient
      (CanonicalBundle.volume.compContinuousLinearMap (refExpDerivative p)) =
        (2 * Real.pi * Complex.I : ℂ) ^ 3 * exponential p.1 := by
  change CanonicalBundle.volume
    (fun i => refExpDerivative p (TrianglePeriodFamily.Canonical.basis i)) = _
  rw [CanonicalBundle.volume_apply, referenceExponential_derivative_matrix]
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ = (2 * Real.pi * Complex.I : ℂ) ^ 3 *
        (refExp p 0 * refExp p 1 * refExp p 2) := by ring
    _ = _ := by rw [referenceExponential_product]

/-- Pullback through the computed derivative, as an equality of actual top covectors. -/
theorem referenceExponential_derivative_volume_pullback (p : LogModel) :
    CanonicalBundle.volume.compContinuousLinearMap (refExpDerivative p) =
      ((2 * Real.pi * Complex.I : ℂ) ^ 3 * exponential p.1) •
        TrianglePeriodFamily.Canonical.volume := by
  calc
    _ = TrianglePeriodFamily.Canonical.coefficient
        (CanonicalBundle.volume.compContinuousLinearMap (refExpDerivative p)) •
          TrianglePeriodFamily.Canonical.volume :=
      TrianglePeriodFamily.Canonical.eq_coefficient_smul_volume _
    _ = _ := by rw [referenceExponential_derivative_volume_coefficient]

/-- The true Fréchet-derivative pullback of the native reference-chart volume. -/
theorem referenceExponential_volume_pullback (p : LogModel) :
    CanonicalBundle.volume.compContinuousLinearMap (fderiv ℂ refExp p) =
      ((2 * Real.pi * Complex.I : ℂ) ^ 3 * exponential p.1) •
        TrianglePeriodFamily.Canonical.volume := by
  rw [fderiv_refExp]
  exact referenceExponential_derivative_volume_pullback p

/-- The same identity for the genuine manifold derivative in the two native models. -/
theorem referenceExponential_mfderiv_volume_pullback (p : LogModel) :
    CanonicalBundle.volume.compContinuousLinearMap
      (mfderiv (modelWithCornersSelf ℂ LogModel)
        (modelWithCornersSelf ℂ CanonicalBundle.Model) refExp p) =
      ((2 * Real.pi * Complex.I : ℂ) ^ 3 * exponential p.1) •
        TrianglePeriodFamily.Canonical.volume := by
  rw [mfderiv_eq_fderiv]
  exact referenceExponential_volume_pullback p

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback
