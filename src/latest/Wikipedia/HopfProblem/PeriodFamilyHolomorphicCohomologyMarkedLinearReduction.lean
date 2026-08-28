import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyMarkedLinearFrame

/-!
# Reduction of four actual period values to the two Dolbeault coordinates

The value of a complex-linear form on the four original period columns
has zero antiholomorphic derivative. Subtracting that form with the
prescribed last two values leaves exactly the first two marked values.
The resulting reduction uses only the original holomorphic period
entries. In particular it has no conjugated period coefficients.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.MarkedLinear

open Complex PeriodTorusLineBundleClassification
open scoped Matrix BigOperators

/-- A genuine complex-linear functional on the original covering plane. -/
def holomorphicLinear (l : Fin 2 → ℂ) : ComplexPlane₂ →L[ℂ] ℂ :=
  ∑ k : Fin 2, l k • ContinuousLinearMap.proj k

@[simp] theorem holomorphicLinear_apply (l : Fin 2 → ℂ) (z : ComplexPlane₂) :
    holomorphicLinear l z = ∑ k : Fin 2, l k * z k := by
  simp [holomorphicLinear, smul_eq_mul]

/-- The original four period values of an actual complex-linear form. -/
def linearValues (p : PeriodDomain) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun l j := ∑ k : Fin 2, l k * p.basis j k
  map_add' a b := by
    ext j
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    ext j
    simp [smul_eq_mul, mul_assoc, mul_add]

@[simp] theorem linearValues_apply (p : PeriodDomain) (l : Fin 2 → ℂ) (j : Fin 4) :
    linearValues p l j = ∑ k : Fin 2, l k * p.basis j k := rfl

/-- The primitive of these values is literally the original complex-linear
form, regarded as real-linear in its spatial argument. -/
theorem primitive_linearValues (p : PeriodDomain) (l : Fin 2 → ℂ) :
    primitive p (linearValues p l) = (holomorphicLinear l).restrictScalars ℝ := by
  have h : (primitive p (linearValues p l)).toLinearMap =
      ((holomorphicLinear l).restrictScalars ℝ).toLinearMap := by
    apply p.basis.ext
    intro j
    exact primitive_basis p (linearValues p l) j
  ext z
  exact LinearMap.congr_fun h z

/-- The native coordinate derivative vanishes on exactly this actual
complex-linear primitive, by complex differentiability. -/
theorem dbarLinear_linearValues (p : PeriodDomain) (l : Fin 2 → ℂ) :
    dbarLinear p (linearValues p l) = 0 := by
  ext i
  rw [← dbarCoordinate_primitive p (linearValues p l) i 0, primitive_linearValues]
  exact dbarCoordinate_zero_of_differentiableAt (holomorphicLinear l).differentiableAt i

/-- The literal period matrix evaluates a complex-linear form on its columns. -/
theorem linearValues_coordinates (p : PeriodDomain) (l : Fin 2 → ℂ) :
    linearValues p l =
      ![6 * p.val.μ * l 0 + p.val.β * l 1,
        p.val.τ * l 0 + p.val.μ * l 1, l 0, l 1] := by
  ext j
  fin_cases j <;>
    simp [linearValues_apply, PeriodDomain.basis_apply, PeriodPoint.matrix,
      Fin.sum_univ_two] <;> ring

/-- The two remaining marked values after removing the original
complex-linear form with the prescribed last two period values. -/
def reduction (p : PeriodDomain) : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun a := ![a 0 - (6 * p.val.μ * a 2 + p.val.β * a 3),
    a 1 - (p.val.τ * a 2 + p.val.μ * a 3)]
  map_add' a b := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c a := by
    ext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

@[simp] theorem reduction_apply (p : PeriodDomain) (a : Fin 4 → ℂ) :
    reduction p a = ![a 0 - (6 * p.val.μ * a 2 + p.val.β * a 3),
      a 1 - (p.val.τ * a 2 + p.val.μ * a 3)] := rfl

/-- Reconstruction preserves all four original lattice coordinates. -/
theorem firstCoefficients_reduction_add_linearValues (p : PeriodDomain) (a : Fin 4 → ℂ) :
    firstCoefficients (reduction p a) + linearValues p ![a 2, a 3] = a := by
  rw [linearValues_coordinates]
  ext j
  fin_cases j <;> simp [firstCoefficients_apply, reduction_apply]

@[simp] theorem reduction_firstCoefficients (p : PeriodDomain) (c : Fin 2 → ℂ) :
    reduction p (firstCoefficients c) = c := by
  ext i
  fin_cases i <;> simp [reduction_apply, firstCoefficients_apply]

/-- The original antiholomorphic coefficients are the proved two-coordinate
marking applied to the holomorphic period reduction. -/
theorem dbarLinear_eq_firstDbar_reduction (p : PeriodDomain) (a : Fin 4 → ℂ) :
    dbarLinear p a = firstDbarEquiv p (reduction p a) := by
  have h := congrArg (dbarLinear p) (firstCoefficients_reduction_add_linearValues p a)
  rw [map_add, dbarLinear_linearValues, add_zero] at h
  exact h.symm

/-- The kernel consists of precisely the actual complex-linear period values. -/
theorem dbarLinear_eq_zero_iff (p : PeriodDomain) (a : Fin 4 → ℂ) :
    dbarLinear p a = 0 ↔ a = linearValues p ![a 2, a 3] := by
  constructor
  · intro ha
    have hr : reduction p a = 0 := by
      apply (firstDbarEquiv p).injective
      simpa only [← dbarLinear_eq_firstDbar_reduction, map_zero] using ha
    have h := firstCoefficients_reduction_add_linearValues p a
    rw [hr, map_zero, zero_add] at h
    exact h.symm
  · intro ha
    rw [ha, dbarLinear_linearValues]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.MarkedLinear
