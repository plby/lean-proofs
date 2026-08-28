import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticShearLinear
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsCoordinates
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalLinear
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsCoefficients

/-!
# Actual alternating-covector coefficients under an elliptic shear

All identities here follow from the genuine continuous alternating covectors
and their actual base-first coordinate basis. A shear fixes the fibre
directions. Its effect on the base direction gives the one-form dot-product
correction and the two-form vertical-area correction. In particular, the
remaining coefficients are unchanged when the corresponding fibre or
vertical coefficient vanishes. The determinant-one calculation fixes every
actual top covector.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates.EllipticShear

@[simp] theorem basis_zero : basis 0 = ((1, 0) : Model) := by
  apply Prod.ext
  · simp [Coordinates.basis, TrianglePeriodFamily.Canonical.basis, Pi.basisFun_apply]
  · funext i
    fin_cases i <;>
      simp [Coordinates.basis, TrianglePeriodFamily.Canonical.basis, Pi.basisFun_apply]

@[simp] theorem basis_succ (i : Fin 2) :
    basis i.succ = ((0, Pi.single i 1) : Model) := by
  apply Prod.ext
  · fin_cases i <;>
      simp [Coordinates.basis, TrianglePeriodFamily.Canonical.basis, Pi.basisFun_apply]
  · funext k
    fin_cases i <;> fin_cases k <;>
      simp [Coordinates.basis, TrianglePeriodFamily.Canonical.basis, Pi.basisFun_apply]

/-- Decomposition in the two genuine vertical basis vectors. -/
theorem vertical_eq_basis (d : ComplexPlane₂) :
    ((0, d) : Model) = d 0 • basis 1 + d 1 • basis 2 := by
  rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
    show (2 : Fin 3) = (1 : Fin 2).succ from rfl, basis_succ, basis_succ]
  apply Prod.ext
  · simp
  · funext i
    fin_cases i <;> simp

@[simp] theorem shear_basis_succ (d : ComplexPlane₂) (i : Fin 2) :
    shear d (basis i.succ) = basis i.succ := by
  rw [basis_succ, shear_vertical]

theorem shear_basis_zero (d : ComplexPlane₂) :
    shear d (basis 0) = basis 0 + ((0, d) : Model) := by
  rw [basis_zero, shear_base]
  simp

/-- Every actual vertical one-form coefficient is fixed by the shear. -/
@[simp] theorem oneFibreCoefficient_pullback
    (a : Model [⋀^Fin 1]→L[ℂ] ℂ) (d : ComplexPlane₂) :
    oneFibreCoefficient (a.compContinuousLinearMap (shear d)) = oneFibreCoefficient a := by
  funext i
  change a (shear d ∘ ![basis i.succ]) = a ![basis i.succ]
  apply congrArg a
  funext k
  fin_cases k
  exact shear_basis_succ d i

/-- The actual vertical-area coefficient is fixed by the shear. -/
@[simp] theorem twoVerticalCoefficient_pullback
    (a : Model [⋀^Fin 2]→L[ℂ] ℂ) (d : ComplexPlane₂) :
    twoVerticalCoefficient (a.compContinuousLinearMap (shear d)) =
      twoVerticalCoefficient a := by
  change a (shear d ∘ ![basis 1, basis 2]) = a ![basis 1, basis 2]
  apply congrArg a
  funext k
  fin_cases k
  · exact shear_basis_succ d 0
  · exact shear_basis_succ d 1

/-- Evaluation on a vertical vector is the genuine fibre covector paired
with that vector. -/
theorem one_vertical_evaluation (a : Model [⋀^Fin 1]→L[ℂ] ℂ) (d : ComplexPlane₂) :
    a ![((0, d) : Model)] = dotProduct (oneFibreCoefficient a) d := by
  rw [vertical_eq_basis d, a.vecCons_add, a.vecCons_smul, a.vecCons_smul]
  change d 0 * oneFibreCoefficient a 0 + d 1 * oneFibreCoefficient a 1 =
    dotProduct (oneFibreCoefficient a) d
  simp only [dotProduct, Fin.sum_univ_two]
  ring

/-- The exact base-coefficient correction, with no assumed transformation law. -/
theorem oneBaseCoefficient_pullback (a : Model [⋀^Fin 1]→L[ℂ] ℂ)
    (d : ComplexPlane₂) :
    oneBaseCoefficient (a.compContinuousLinearMap (shear d)) =
      oneBaseCoefficient a + dotProduct (oneFibreCoefficient a) d := by
  change a (shear d ∘ ![basis 0]) =
    a ![basis 0] + dotProduct (oneFibreCoefficient a) d
  have hv : shear d ∘ ![basis 0] = ![basis 0 + ((0, d) : Model)] := by
    funext k
    fin_cases k
    exact shear_basis_zero d
  rw [hv, a.vecCons_add, one_vertical_evaluation]

theorem oneBaseCoefficient_pullback_of_oneFibreCoefficient_eq_zero
    (a : Model [⋀^Fin 1]→L[ℂ] ℂ) (d : ComplexPlane₂)
    (ha : oneFibreCoefficient a = 0) :
    oneBaseCoefficient (a.compContinuousLinearMap (shear d)) = oneBaseCoefficient a := by
  rw [oneBaseCoefficient_pullback, ha, zero_dotProduct, add_zero]

private theorem two_self (a : Model [⋀^Fin 2]→L[ℂ] ℂ) (x : Model) :
    a ![x, x] = 0 :=
  a.map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)

private theorem two_swap (a : Model [⋀^Fin 2]→L[ℂ] ℂ) (x y : Model) :
    a ![y, x] = -a ![x, y] := by
  have h := a.toAlternatingMap.map_swap ![x, y] (i := 0) (j := 1) (by decide)
  have hv : ![x, y] ∘ Equiv.swap (0 : Fin 2) 1 = ![y, x] := by
    funext k
    fin_cases k <;> simp
  rw [hv] at h
  exact h

/-- Alternation identifies the vertical contribution to each mixed coefficient. -/
theorem two_vertical_evaluation (a : Model [⋀^Fin 2]→L[ℂ] ℂ)
    (d : ComplexPlane₂) (i : Fin 2) :
    a ![((0, d) : Model), basis i.succ] =
      twoVerticalCoefficient a * PeriodFamilyHolomorphicForms.skewPeriod d i := by
  rw [vertical_eq_basis d, a.vecCons_add, a.vecCons_smul, a.vecCons_smul]
  fin_cases i
  · change d 0 • a ![basis 1, basis 1] + d 1 • a ![basis 2, basis 1] =
      twoVerticalCoefficient a * (-d 1)
    rw [two_self, two_swap a (basis 1) (basis 2)]
    change d 0 * 0 + d 1 * (-twoVerticalCoefficient a) =
      twoVerticalCoefficient a * (-d 1)
    ring
  · change d 0 • a ![basis 1, basis 2] + d 1 • a ![basis 2, basis 2] =
      twoVerticalCoefficient a * d 0
    rw [two_self]
    change d 0 * twoVerticalCoefficient a + d 1 * 0 = twoVerticalCoefficient a * d 0
    ring

/-- The exact mixed-coefficient correction is the vertical area coefficient
times the actual skew of the shear vector. -/
theorem twoMixedCoefficient_pullback (a : Model [⋀^Fin 2]→L[ℂ] ℂ)
    (d : ComplexPlane₂) :
    twoMixedCoefficient (a.compContinuousLinearMap (shear d)) =
      twoMixedCoefficient a +
        twoVerticalCoefficient a • PeriodFamilyHolomorphicForms.skewPeriod d := by
  funext i
  change a (shear d ∘ ![basis 0, basis i.succ]) =
    a ![basis 0, basis i.succ] +
      twoVerticalCoefficient a * PeriodFamilyHolomorphicForms.skewPeriod d i
  have hv : shear d ∘ ![basis 0, basis i.succ] =
      ![basis 0 + ((0, d) : Model), basis i.succ] := by
    funext k
    fin_cases k
    · exact shear_basis_zero d
    · exact shear_basis_succ d i
  rw [hv, a.vecCons_add, two_vertical_evaluation]

theorem twoMixedCoefficient_pullback_of_twoVerticalCoefficient_eq_zero
    (a : Model [⋀^Fin 2]→L[ℂ] ℂ) (d : ComplexPlane₂)
    (ha : twoVerticalCoefficient a = 0) :
    twoMixedCoefficient (a.compContinuousLinearMap (shear d)) = twoMixedCoefficient a := by
  rw [twoMixedCoefficient_pullback, ha, zero_smul, add_zero]

/-- The actual shear is the already-computed determinant-one block map. -/
theorem shear_eq_shearDerivative (d : ComplexPlane₂) :
    shear d = TrianglePeriodFamily.Canonical.shearDerivative d := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [shear_apply, TrianglePeriodFamily.Canonical.shearDerivative_apply, add_comm]

/-- A determinant-one shear fixes every genuine continuous top covector. -/
@[simp] theorem top_pullback (a : Model [⋀^Fin 3]→L[ℂ] ℂ) (d : ComplexPlane₂) :
    a.compContinuousLinearMap (shear d) = a := by
  rw [shear_eq_shearDerivative]
  exact TrianglePeriodFamily.Canonical.pullback_shearDerivative a d

@[simp] theorem topCoefficient_pullback (a : Model [⋀^Fin 3]→L[ℂ] ℂ)
    (d : ComplexPlane₂) :
    topCoefficient (a.compContinuousLinearMap (shear d)) = topCoefficient a := by
  rw [top_pullback]

end Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates.EllipticShear
