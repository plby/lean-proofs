import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticShearCoefficients

/-!
# Actual alternating-covector coefficients under a base change

The continuous linear map scales the actual base coordinate and fixes both
actual fibre coordinates. Evaluating genuine alternating covectors on the
base-first basis gives all five coefficient identities by multilinearity.
These identities hold for every complex scaling factor, including zero;
no invertibility or coefficient transformation law is an input.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates.EllipticBaseChange

/-- The genuine linear base scaling on the original product model. -/
def baseChange (c : ℂ) : Model →L[ℂ] Model :=
  (c • ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂).prod
    (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂)

@[simp] theorem baseChange_apply (c : ℂ) (w : Model) :
    baseChange c w = (c * w.1, w.2) := rfl

@[simp] theorem baseChange_basis_zero (c : ℂ) :
    baseChange c (basis 0) = c • basis 0 := by
  rw [EllipticShear.basis_zero, baseChange_apply]
  simp

@[simp] theorem baseChange_basis_succ (c : ℂ) (i : Fin 2) :
    baseChange c (basis i.succ) = basis i.succ := by
  rw [EllipticShear.basis_succ, baseChange_apply]
  simp

/-- Both genuine fibre one-form coefficients are unchanged. -/
@[simp] theorem oneFibreCoefficient_pullback
    (a : Model [⋀^Fin 1]→L[ℂ] ℂ) (c : ℂ) :
    oneFibreCoefficient (a.compContinuousLinearMap (baseChange c)) =
      oneFibreCoefficient a := by
  funext i
  change a (baseChange c ∘ ![basis i.succ]) = a ![basis i.succ]
  apply congrArg a
  funext k
  fin_cases k
  exact baseChange_basis_succ c i

/-- Scaling the actual base vector scales its one-form coefficient. -/
theorem oneBaseCoefficient_pullback (a : Model [⋀^Fin 1]→L[ℂ] ℂ) (c : ℂ) :
    oneBaseCoefficient (a.compContinuousLinearMap (baseChange c)) =
      c * oneBaseCoefficient a := by
  change a (baseChange c ∘ ![basis 0]) = c * a ![basis 0]
  have hv : baseChange c ∘ ![basis 0] = ![c • basis 0] := by
    funext k
    fin_cases k
    exact baseChange_basis_zero c
  rw [hv, a.vecCons_smul, smul_eq_mul]

/-- The actual vertical-area coefficient does not involve the base vector. -/
@[simp] theorem twoVerticalCoefficient_pullback
    (a : Model [⋀^Fin 2]→L[ℂ] ℂ) (c : ℂ) :
    twoVerticalCoefficient (a.compContinuousLinearMap (baseChange c)) =
      twoVerticalCoefficient a := by
  change a (baseChange c ∘ ![basis 1, basis 2]) = a ![basis 1, basis 2]
  apply congrArg a
  funext k
  fin_cases k
  · exact baseChange_basis_succ c 0
  · exact baseChange_basis_succ c 1

/-- Both mixed coefficients scale by exactly the actual base factor. -/
theorem twoMixedCoefficient_pullback (a : Model [⋀^Fin 2]→L[ℂ] ℂ) (c : ℂ) :
    twoMixedCoefficient (a.compContinuousLinearMap (baseChange c)) =
      c • twoMixedCoefficient a := by
  funext i
  change a (baseChange c ∘ ![basis 0, basis i.succ]) = c * a ![basis 0, basis i.succ]
  have hv : baseChange c ∘ ![basis 0, basis i.succ] = ![c • basis 0, basis i.succ] := by
    funext k
    fin_cases k
    · exact baseChange_basis_zero c
    · exact baseChange_basis_succ c i
  rw [hv, a.vecCons_smul, smul_eq_mul]

/-- Multilinearity in the actual base vector gives the top-coefficient
formula, also when the scaling factor is zero. -/
theorem topCoefficient_pullback (a : Model [⋀^Fin 3]→L[ℂ] ℂ) (c : ℂ) :
    topCoefficient (a.compContinuousLinearMap (baseChange c)) = c * topCoefficient a := by
  change a (baseChange c ∘ ![basis 0, basis 1, basis 2]) = c * a ![basis 0, basis 1, basis 2]
  have hv : baseChange c ∘ ![basis 0, basis 1, basis 2] =
      ![c • basis 0, basis 1, basis 2] := by
    funext k
    fin_cases k
    · exact baseChange_basis_zero c
    · exact baseChange_basis_succ c 0
    · exact baseChange_basis_succ c 1
  rw [hv, a.vecCons_smul, smul_eq_mul]

end Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates.EllipticBaseChange
