import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianBasis
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierPeriodCoordinates

/-!
# Antiholomorphic derivatives of real alternating forms

The coefficients below are actual real continuous linear maps on the
covering plane. Their mixed antiholomorphic derivative measures precisely
the failure of a real alternating form to have type `(1,1)`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex PeriodTorusTypeOneOne

/-- The antiholomorphic derivative in the first slot, as a real-linear
function of the second slot. -/
def realFormDbarLinear (B : RealForm) (i : Fin 2) : ComplexPlane₂ →L[ℝ] ℂ :=
  (1 / (2 : ℂ)) •
    (Complex.ofRealCLM.comp (B (Pi.single i 1)).toContinuousLinearMap +
      I • Complex.ofRealCLM.comp (B (I • Pi.single i 1)).toContinuousLinearMap)

@[simp]
theorem realFormDbarLinear_apply (B : RealForm) (i : Fin 2) (z : ComplexPlane₂) :
    realFormDbarLinear B i z =
      ((B (Pi.single i 1) z : ℂ) + I * (B (I • Pi.single i 1) z : ℂ)) / 2 := by
  change (1 / (2 : ℂ)) *
    ((B (Pi.single i 1) z : ℂ) + I * (B (I • Pi.single i 1) z : ℂ)) = _
  ring

/-- Differentiating the literal real-form evaluation gives the constructed
coefficient, independently of the base point. -/
theorem dbarCoordinate_realForm_eval (B : RealForm) (y z : ComplexPlane₂) (i : Fin 2) :
    dbarCoordinate (fun x => (B x y : ℂ)) i z = realFormDbarLinear B i y := by
  let L := Complex.ofRealCLM.comp (B.flip y).toContinuousLinearMap
  change dbarCoordinate L i z = _
  rw [dbarCoordinate_eq_fderiv L.differentiableAt, L.fderiv]
  rw [realFormDbarLinear_apply]
  rfl

theorem dbarCoordinate_realFormDbarLinear (B : RealForm) (i j : Fin 2)
    (z : ComplexPlane₂) :
    dbarCoordinate (realFormDbarLinear B j) i z =
      (realFormDbarLinear B j (Pi.single i 1) +
        I * realFormDbarLinear B j (I • Pi.single i 1)) / 2 := by
  rw [dbarCoordinate_eq_fderiv (realFormDbarLinear B j).differentiableAt,
    (realFormDbarLinear B j).fderiv]

private theorem coordinate_zero_eq_e0 : (Pi.single 0 1 : ComplexPlane₂) = e0 := by
  ext i
  fin_cases i <;> simp [e0]

private theorem coordinate_one_eq_e1 : (Pi.single 1 1 : ComplexPlane₂) = e1 := by
  ext i
  fin_cases i <;> simp [e1]

/-- The mixed derivative is the actual `(0,2)` component, with its exact sign. -/
theorem realFormDbarLinear_mixed_difference (B : RealForm) (hAlt : ∀ x, B x x = 0)
    (z : ComplexPlane₂) :
    dbarCoordinate (realFormDbarLinear B 1) 0 z -
        dbarCoordinate (realFormDbarLinear B 0) 1 z =
      -(((B e0 e1 : ℂ) - (B (I • e0) (I • e1) : ℂ)) +
        I * ((B (I • e0) e1 : ℂ) + (B e0 (I • e1) : ℂ))) / 2 := by
  simp only [dbarCoordinate_realFormDbarLinear, realFormDbarLinear_apply,
    coordinate_zero_eq_e0, coordinate_one_eq_e1]
  rw [realForm_skew B hAlt e1 e0, realForm_skew B hAlt (I • e1) e0,
    realForm_skew B hAlt e1 (I • e0), realForm_skew B hAlt (I • e1) (I • e0)]
  simp only [Complex.ofReal_neg]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Vanishing of the actual mixed derivative forces type `(1,1)`; there is
no type condition in the hypotheses hidden in the definition of the model. -/
theorem isTypeOneOne_of_realFormDbarLinear_closed (B : RealForm)
    (hAlt : ∀ x, B x x = 0)
    (hclosed : dbarCoordinate (realFormDbarLinear B 1) 0 0 =
      dbarCoordinate (realFormDbarLinear B 0) 1 0) : IsTypeOneOne B := by
  apply (isTypeOneOne_iff_basis B hAlt).mpr
  have h := realFormDbarLinear_mixed_difference B hAlt 0
  rw [hclosed, sub_self] at h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp at hr hi
  constructor
  · linarith only [hr]
  · linarith only [hi]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
