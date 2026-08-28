import Wikipedia.HopfProblem.SpecialPeriodsTriangleCusp

/-!
# Horizontal translation in the actual cusp coordinate

Translation by a positive fraction of the cusp width becomes positive
rotation under the exponential cusp coordinate.  The imaginary part,
and therefore the modulus of the cusp coordinate, stays fixed.
-/

noncomputable section

open UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods

/-- Moving horizontally by `width * s` multiplies the actual cusp
coordinate by the positive exponential turn. -/
theorem cuspQ_horizontal_translate (z : ℍ) (s : ℝ) :
    Triangle.cuspQ ((Triangle.width * s) +ᵥ z) =
      Triangle.cuspQ z * Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) := by
  rw [Triangle.cuspQ_eq_exp, Triangle.cuspQ_eq_exp, ← Complex.exp_add]
  congr 1
  rw [UpperHalfPlane.coe_vadd, Complex.ofReal_mul]
  have hw : (Triangle.width : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Triangle.width_ne_zero
  field_simp [hw]
  ring

/-- Horizontal translation preserves the modulus of the cusp
coordinate, so the resulting exponential path lies on one circle. -/
theorem cuspQ_horizontal_translate_norm (z : ℍ) (s : ℝ) :
    ‖Triangle.cuspQ ((Triangle.width * s) +ᵥ z)‖ = ‖Triangle.cuspQ z‖ := by
  rw [Triangle.cuspQ_norm, Triangle.cuspQ_norm, UpperHalfPlane.vadd_im]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
