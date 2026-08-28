import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationRealModelDbar
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationRealModelCalculus
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTypeOneOneAveraging

/-!
# The type `(1,1)` obstruction vanishes by actual torus averaging

Subtracting a smooth logarithmic model gives affine-periodic
antiholomorphic derivatives. Their corrected periodic coefficients have a
constant mixed derivative. The actual Haar/Fourier mean forces this
constant to vanish, hence forces the original real alternating form to
have type `(1,1)`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex PeriodTorusTypeOneOne
open scoped ContDiff

def realFormCorrectedDbar (B : RealForm) (h : ComplexPlane₂ → ℂ)
    (i : Fin 2) (z : ComplexPlane₂) : ℂ :=
  dbarCoordinate h i z + (Real.pi : ℂ) * I * realFormDbarLinear B i z

theorem contDiff_realFormCorrectedDbar (B : RealForm) {h : ComplexPlane₂ → ℂ}
    (hh : ContDiff ℝ ∞ h) (i : Fin 2) : ContDiff ℝ ∞ (realFormCorrectedDbar B h i) :=
  (contDiff_dbarCoordinate hh i).add
    (contDiff_const.mul (realFormDbarLinear B i).contDiff)

theorem realFormCorrectedDbar_mixed_difference (B : RealForm) {h : ComplexPlane₂ → ℂ}
    (hh : ContDiff ℝ ∞ h) (z : ComplexPlane₂) :
    dbarCoordinate (realFormCorrectedDbar B h 1) 0 z -
        dbarCoordinate (realFormCorrectedDbar B h 0) 1 z =
      (Real.pi : ℂ) * I * (dbarCoordinate (realFormDbarLinear B 1) 0 0 -
        dbarCoordinate (realFormDbarLinear B 0) 1 0) := by
  have hD (i : Fin 2) : DifferentiableAt ℝ
      (fun x => (Real.pi : ℂ) * I * realFormDbarLinear B i x) z :=
    (realFormDbarLinear B i).differentiableAt.const_mul _
  change dbarCoordinate (fun x => dbarCoordinate h 1 x +
      (Real.pi : ℂ) * I * realFormDbarLinear B 1 x) 0 z -
    dbarCoordinate (fun x => dbarCoordinate h 0 x +
      (Real.pi : ℂ) * I * realFormDbarLinear B 0 x) 1 z = _
  rw [dbarCoordinate_add ((contDiff_dbarCoordinate hh 1).differentiable (by simp) z) (hD 1),
    dbarCoordinate_add ((contDiff_dbarCoordinate hh 0).differentiable (by simp) z) (hD 0),
    dbarCoordinate_const_mul (realFormDbarLinear B 1).differentiableAt,
    dbarCoordinate_const_mul (realFormDbarLinear B 0).differentiableAt,
    dbarCoordinate_zero_one_commute hh z]
  simp only [dbarCoordinate_realFormDbarLinear]
  ring

/-- The type condition is a consequence of smoothness and actual periodicity
of the corrected derivative; it is not part of the model data. -/
theorem isTypeOneOne_of_periodic_correctedDbar (p : PeriodDomain) (B : RealForm)
    (hAlt : ∀ x, B x x = 0) {h : ComplexPlane₂ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hperiodic : ∀ i : Fin 2, ∀ z : ComplexPlane₂, ∀ l : p.lattice,
      realFormCorrectedDbar B h i (z + l) = realFormCorrectedDbar B h i z) :
    IsTypeOneOne B := by
  have hc := constant_eq_zero_of_periodic_dbar_difference p
    (realFormCorrectedDbar B h 0) (realFormCorrectedDbar B h 1)
    (contDiff_realFormCorrectedDbar B hh 0) (contDiff_realFormCorrectedDbar B hh 1)
    (hperiodic 0) (hperiodic 1) 0 1 _ (realFormCorrectedDbar_mixed_difference B hh)
  have hpi : (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero
  have hz := (mul_eq_zero.mp hc).resolve_left hpi
  exact isTypeOneOne_of_realFormDbarLinear_closed B hAlt (sub_eq_zero.mp hz)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
