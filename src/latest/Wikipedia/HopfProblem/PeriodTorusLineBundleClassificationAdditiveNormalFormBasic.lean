import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationRealModelCalculus
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCharacterBasic

/-!
# Explicit primitives of the constant antiholomorphic modes

The constant Fourier modes have an actual antilinear primitive on the
covering vector space. Its additive lattice increments exponentiate to
a genuine unit-valued lattice character.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex

def antiholomorphicLinear (c : Fin 2 → ℂ) : ComplexPlane₂ →L[ℝ] ℂ :=
  c 0 • (Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj 0)) +
    c 1 • (Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj 1))

@[simp]
theorem antiholomorphicLinear_apply (c : Fin 2 → ℂ) (z : ComplexPlane₂) :
    antiholomorphicLinear c z = c 0 * star (z 0) + c 1 * star (z 1) := rfl

theorem dbarCoordinate_antiholomorphicLinear (c : Fin 2 → ℂ) (i : Fin 2)
    (z : ComplexPlane₂) : dbarCoordinate (antiholomorphicLinear c) i z = c i := by
  rw [dbarCoordinate_eq_fderiv (antiholomorphicLinear c).differentiableAt,
    (antiholomorphicLinear c).fderiv]
  simp only [antiholomorphicLinear_apply]
  fin_cases i <;> simp [smul_eq_mul]
  all_goals ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring

/-- Exponentiating an actual real-linear functional gives a genuine character
of the actual lattice. Complex linearity is not required for this step. -/
def realLinearExponentialCharacter {p : PeriodDomain} (L : ComplexPlane₂ →ₗ[ℝ] ℂ) :
    LatticeCharacter p where
  toFun g := Units.mk0 (Complex.exp (L ((Multiplicative.toAdd g : p.lattice) : ComplexPlane₂)))
    (Complex.exp_ne_zero _)
  map_one' := by
    apply Units.ext
    change Complex.exp (L (0 : ComplexPlane₂)) = 1
    simp
  map_mul' g h := by
    apply Units.ext
    change Complex.exp (L ((Multiplicative.toAdd g + Multiplicative.toAdd h : p.lattice) :
      ComplexPlane₂)) = Complex.exp (L ((Multiplicative.toAdd g : p.lattice) : ComplexPlane₂)) *
        Complex.exp (L ((Multiplicative.toAdd h : p.lattice) : ComplexPlane₂))
    rw [Submodule.coe_add, map_add, Complex.exp_add]

@[simp]
theorem realLinearExponentialCharacter_value {p : PeriodDomain}
    (L : ComplexPlane₂ →ₗ[ℝ] ℂ) (l : p.lattice) :
    characterValue (realLinearExponentialCharacter L) l = Complex.exp (L (l : ComplexPlane₂)) :=
  rfl

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
