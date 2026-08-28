import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationRealModelCalculus

/-!
# Actual antiholomorphic coefficients of the marked period primitives

A complex-valued character of the four marked real period coordinates
defines an actual real-linear function on the original covering plane.
Its antiholomorphic differential is computed using the original coordinate
derivative. This is a calculation on the genuine covering space; no
family base-change assertion is made here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.MarkedLinear

open Complex PeriodTorusLineBundleClassification
open scoped BigOperators

/-- The original real-linear primitive with four prescribed complex
values on the marked period basis. -/
def primitive (p : PeriodDomain) (a : Fin 4 → ℂ) : ComplexPlane₂ →L[ℝ] ℂ :=
  ∑ j : Fin 4, a j •
    (Complex.ofRealCLM.comp
      ((ContinuousLinearMap.proj j).comp
        (PeriodTorusTypeOneOne.periodEquiv p).symm.toContinuousLinearEquiv.toContinuousLinearMap))

@[simp] theorem primitive_apply (p : PeriodDomain) (a : Fin 4 → ℂ)
    (z : ComplexPlane₂) :
    primitive p a z = ∑ j : Fin 4, a j *
      (((PeriodTorusTypeOneOne.periodEquiv p).symm z j : ℝ) : ℂ) := by
  simp [primitive, smul_eq_mul]

/-- Evaluation on the actual period map recovers the original marked
linear combination, without a change of coordinates. -/
@[simp] theorem primitive_periodEquiv (p : PeriodDomain) (a : Fin 4 → ℂ)
    (v : Fin 4 → ℝ) :
    primitive p a (PeriodTorusTypeOneOne.periodEquiv p v) =
      ∑ j : Fin 4, a j * (v j : ℂ) := by
  simp only [primitive_apply, LinearEquiv.symm_apply_apply]

@[simp] theorem primitive_basis (p : PeriodDomain) (a : Fin 4 → ℂ) (j : Fin 4) :
    primitive p a (p.basis j) = a j := by
  rw [← PeriodTorusTypeOneOne.periodEquiv_single, primitive_periodEquiv]
  simp [Pi.single_apply, apply_ite]

/-- The actual covering-space primitive depends complex-linearly on its
four marked values. Its spatial argument is only real-linear. -/
def primitiveLinear (p : PeriodDomain) :
    (Fin 4 → ℂ) →ₗ[ℂ] (ComplexPlane₂ →L[ℝ] ℂ) where
  toFun := primitive p
  map_add' a b := by
    ext z
    simp [primitive_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    ext z
    simp [primitive_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

@[simp] theorem primitiveLinear_apply (p : PeriodDomain) (a : Fin 4 → ℂ) :
    primitiveLinear p a = primitive p a := rfl

/-- The pair of literal antiholomorphic coordinate coefficients. -/
def dbarLinear (p : PeriodDomain) : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun a i := dbarCoordinateLinear i (primitive p a)
  map_add' a b := by
    funext i
    change dbarCoordinateLinear i (primitiveLinear p (a + b)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c a := by
    funext i
    change dbarCoordinateLinear i (primitiveLinear p (c • a)) = _
    rw [map_smul, dbarCoordinateLinear_complex_smul]
    rfl

@[simp] theorem dbarLinear_apply (p : PeriodDomain) (a : Fin 4 → ℂ) (i : Fin 2) :
    dbarLinear p a i =
      (primitive p a (Pi.single i 1) +
        I * primitive p a (I • Pi.single i 1)) / 2 :=
  dbarCoordinateLinear_apply i (primitive p a)

/-- The original coordinate-update derivative of the genuine primitive
is this constant pair at every point of the covering plane. -/
theorem dbarCoordinate_primitive (p : PeriodDomain) (a : Fin 4 → ℂ)
    (i : Fin 2) (z : ComplexPlane₂) :
    dbarCoordinate (primitive p a) i z = dbarLinear p a i := by
  rw [dbarCoordinate_eq_linear (primitive p a).differentiableAt,
    (primitive p a).fderiv]
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.MarkedLinear
