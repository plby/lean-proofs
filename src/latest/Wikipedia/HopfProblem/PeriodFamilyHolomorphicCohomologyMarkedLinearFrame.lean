import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyMarkedLinearBasic
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianBasic

/-!
# The two first marked period coordinates give an actual Dolbeault frame

The last two original period columns are the real coordinate vectors
of the covering plane. A primitive supported in the first two marked
period coordinates therefore vanishes on both real coordinate vectors.
If its antiholomorphic coefficients vanish too, all four real directions
vanish. This proves the claimed complex-linear isomorphism directly from
the original period basis, not from a dimension assigned to cohomology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.MarkedLinear

open Complex PeriodTorusLineBundleClassification
open scoped Matrix BigOperators

/-- Retain the first two marked lattice values and set the last two to zero. -/
def firstCoefficients : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun c := ![c 0, c 1, 0, 0]
  map_add' a b := by ext j; fin_cases j <;> simp
  map_smul' c a := by ext j; fin_cases j <;> simp

@[simp] theorem firstCoefficients_apply (c : Fin 2 → ℂ) :
    firstCoefficients c = ![c 0, c 1, 0, 0] := rfl

theorem period_basis_two (p : PeriodDomain) : p.basis 2 = Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [PeriodDomain.basis_apply, PeriodPoint.matrix]

theorem period_basis_three (p : PeriodDomain) : p.basis 3 = Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp [PeriodDomain.basis_apply, PeriodPoint.matrix]

/-- The actual primitive of the first two marked coordinates vanishes
on the two original real coordinate directions of the covering plane. -/
theorem primitive_firstCoefficients_realDirection (p : PeriodDomain) (c : Fin 2 → ℂ)
    (i : Fin 2) : primitive p (firstCoefficients c) (Pi.single i 1) = 0 := by
  fin_cases i
  · change primitive p (firstCoefficients c) (Pi.single (0 : Fin 2) (1 : ℂ)) = 0
    rw [← period_basis_two p, primitive_basis]
    rfl
  · change primitive p (firstCoefficients c) (Pi.single (1 : Fin 2) (1 : ℂ)) = 0
    rw [← period_basis_three p, primitive_basis]
    rfl

private theorem realLinear_zero_of_coordinate_values (L : ComplexPlane₂ →L[ℝ] ℂ)
    (hRe : ∀ i : Fin 2, L (Pi.single i 1) = 0)
    (hIm : ∀ i : Fin 2, L (I • Pi.single i 1) = 0) : L = 0 := by
  ext z
  have hDirection (i : Fin 2) : L (z i • Pi.single i 1) = 0 := by
    rw [PeriodTorusTypeOneOne.complex_smul_decomposition]
    simp only [map_add, map_smul, hRe, hIm, smul_zero, add_zero]
  conv_lhs => rw [pi_eq_sum_univ' z, map_sum]
  simp only [hDirection, Finset.sum_const_zero, zero_apply]

/-- The actual pair of antiholomorphic coefficients of these two
marked covering-space primitives. -/
def firstDbarLinear (p : PeriodDomain) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  (dbarLinear p).comp firstCoefficients

@[simp] theorem firstDbarLinear_apply (p : PeriodDomain) (c : Fin 2 → ℂ) :
    firstDbarLinear p c = dbarLinear p (firstCoefficients c) := rfl

/-- Both actual antiholomorphic coefficients determine the two original
marked period values injectively. -/
theorem firstDbarLinear_injective (p : PeriodDomain) :
    Function.Injective (firstDbarLinear p) := by
  apply (injective_iff_map_eq_zero (firstDbarLinear p)).mpr
  intro c hc
  have hRe := primitive_firstCoefficients_realDirection p c
  have hIm (i : Fin 2) : primitive p (firstCoefficients c) (I • Pi.single i 1) = 0 := by
    have h := congrFun hc i
    change dbarLinear p (firstCoefficients c) i = 0 at h
    rw [dbarLinear_apply, hRe i, zero_add, div_eq_zero_iff] at h
    exact (mul_eq_zero.mp (h.resolve_right (by norm_num))).resolve_left I_ne_zero
  have hL := realLinear_zero_of_coordinate_values
    (primitive p (firstCoefficients c)) hRe hIm
  have h0 : c 0 = 0 := by
    have h := congrArg (fun L : ComplexPlane₂ →L[ℝ] ℂ => L (p.basis 0)) hL
    simpa only [primitive_basis, firstCoefficients_apply, Matrix.cons_val_zero,
      zero_apply] using h
  have h1 : c 1 = 0 := by
    have h := congrArg (fun L : ComplexPlane₂ →L[ℝ] ℂ => L (p.basis 1)) hL
    simpa only [primitive_basis, firstCoefficients_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, zero_apply] using h
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- Surjectivity follows from the proved injectivity of the actual
linear operator between the two original coordinate-pair spaces. -/
theorem firstDbarLinear_bijective (p : PeriodDomain) :
    Function.Bijective (firstDbarLinear p) :=
  ⟨firstDbarLinear_injective p,
    LinearMap.injective_iff_surjective.mp (firstDbarLinear_injective p)⟩

/-- The actual first-coordinate Dolbeault marking, with the unchanged
positive coordinate-derivative convention. -/
def firstDbarEquiv (p : PeriodDomain) : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearEquiv.ofBijective (firstDbarLinear p) (firstDbarLinear_bijective p)

@[simp] theorem firstDbarEquiv_apply (p : PeriodDomain) (c : Fin 2 → ℂ) :
    firstDbarEquiv p c = dbarLinear p (firstCoefficients c) := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.MarkedLinear
