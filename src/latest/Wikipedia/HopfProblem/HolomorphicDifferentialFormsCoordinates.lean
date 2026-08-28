import Wikipedia.HopfProblem.HolomorphicDifferentialFormsFunctor
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalAlternating

/-!
# Actual period-coordinate coefficients of differential forms

The ordered model coordinates are (base, first fibre, second fibre).
Every coefficient is evaluation of a genuine alternating covector on
the corresponding actual basis vectors. All coefficient maps are
continuous and complex linear.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates

abbrev Model := ℂ × ComplexPlane₂

abbrev basis : Module.Basis (Fin 3) ℂ Model := TrianglePeriodFamily.Canonical.basis

/-- Coefficient of dz in an actual one-covector. -/
def oneBaseCoefficient : (Model [⋀^Fin 1]→L[ℂ] ℂ) →L[ℂ] ℂ :=
  ContinuousAlternatingMap.apply ℂ Model ℂ ![basis 0]

/-- Coefficients of dζ₁ and dζ₂ in an actual one-covector. -/
def oneFibreCoefficient : (Model [⋀^Fin 1]→L[ℂ] ℂ) →L[ℂ] ComplexPlane₂ :=
  ContinuousLinearMap.pi fun i : Fin 2 =>
    ContinuousAlternatingMap.apply ℂ Model ℂ ![basis i.succ]

/-- Coefficient of dζ₁∧dζ₂ in an actual two-covector. -/
def twoVerticalCoefficient : (Model [⋀^Fin 2]→L[ℂ] ℂ) →L[ℂ] ℂ :=
  ContinuousAlternatingMap.apply ℂ Model ℂ ![basis 1, basis 2]

/-- Coefficients of dz∧dζ₁ and dz∧dζ₂ in an actual two-covector. -/
def twoMixedCoefficient : (Model [⋀^Fin 2]→L[ℂ] ℂ) →L[ℂ] ComplexPlane₂ :=
  ContinuousLinearMap.pi fun i : Fin 2 =>
    ContinuousAlternatingMap.apply ℂ Model ℂ ![basis 0, basis i.succ]

/-- Coefficient of dz∧dζ₁∧dζ₂ in an actual top covector. -/
def topCoefficient : (Model [⋀^Fin 3]→L[ℂ] ℂ) →L[ℂ] ℂ :=
  ContinuousAlternatingMap.apply ℂ Model ℂ ![basis 0, basis 1, basis 2]

@[simp] theorem oneBaseCoefficient_apply (a : Model [⋀^Fin 1]→L[ℂ] ℂ) :
    oneBaseCoefficient a = a ![basis 0] := rfl

@[simp] theorem oneFibreCoefficient_apply (a : Model [⋀^Fin 1]→L[ℂ] ℂ) (i : Fin 2) :
    oneFibreCoefficient a i = a ![basis i.succ] := rfl

@[simp] theorem twoVerticalCoefficient_apply (a : Model [⋀^Fin 2]→L[ℂ] ℂ) :
    twoVerticalCoefficient a = a ![basis 1, basis 2] := rfl

@[simp] theorem twoMixedCoefficient_apply (a : Model [⋀^Fin 2]→L[ℂ] ℂ) (i : Fin 2) :
    twoMixedCoefficient a i = a ![basis 0, basis i.succ] := rfl

@[simp] theorem topCoefficient_apply (a : Model [⋀^Fin 3]→L[ℂ] ℂ) :
    topCoefficient a = a ![basis 0, basis 1, basis 2] := rfl

end Wikipedia.HopfProblem.HolomorphicDifferentialForms.Coordinates
