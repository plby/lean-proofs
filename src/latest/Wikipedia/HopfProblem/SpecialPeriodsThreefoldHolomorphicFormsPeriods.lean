import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCoefficients
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsDerivatives
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticRestriction

/-!
# The actual period identities on the regular cover

All translations here belong to the original full integral period
lattice. They fix the genuine point of the constructed threefold.
Restriction to the free regular base also preserves the actual native
period derivatives, by the derivative of its inherited open inclusion.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

/-- Adding a vector in the actual full period lattice changes neither
the actual torus point nor either later quotient. -/
theorem globalCover_add_lattice (z : TriangleRegularPoint) (ζ w : ComplexPlane₂)
    (hw : w ∈ (data.periods.point z).lattice) :
    globalCover (z, ζ + w) = globalCover (z, ζ) := by
  apply congrArg regularFamilyInclusion
  apply congrArg data.quotient
  rw [← data.periods.fibreInclusion_mkQ, ← data.periods.fibreInclusion_mkQ]
  exact congrArg (data.periods.fibreInclusion z)
    (PeriodTorusQuasiperiodic.quotient_add_lattice _ ζ w hw)

/-- Every original integral period fixes the actual global covering map. -/
theorem globalCover_add_period (z : TriangleRegularPoint) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    globalCover (z, ζ + PeriodFamilyHolomorphicForms.periodShift data.periods z ℓ) =
      globalCover (z, ζ) := by
  apply globalCover_add_lattice
  rw [PeriodFamilyHolomorphicForms.periodShift_eq_matrix]
  exact PeriodTorusQuasiperiodic.integer_period_mem_lattice _ ℓ

/-- The restricted shift is the very same original period vector. -/
theorem periodShift_eq (z : TriangleRegularPoint) (ℓ : Lattice) :
    PeriodFamilyHolomorphicForms.periodShift data.periods z ℓ =
      PeriodFamilyHolomorphicForms.periodShift specialPeriodMap z.val ℓ := rfl

/-- The period derivative in the original regular coordinate is the
restriction of the original upper-half-plane derivative. -/
theorem periodDerivative_eq (z : TriangleRegularPoint) (ℓ : Lattice) :
    PeriodFamilyHolomorphicForms.periodDerivative data.periods z ℓ =
      PeriodFamilyHolomorphicForms.periodDerivative specialPeriodMap z.val ℓ := by
  have hg :=
    (PeriodFamilyHolomorphicForms.periodShift_holomorphic specialPeriodMap ℓ).mdifferentiable
      (by simp) z.val
  have hf := (contMDiff_subtype_val (I := I₁) (n := ω)
    (U := triangleRegularDomain)).mdifferentiable (by simp) z
  have h := mfderiv_comp_apply z (g := fun b : ℍ =>
    PeriodFamilyHolomorphicForms.periodShift specialPeriodMap b ℓ)
    (f := (Subtype.val : TriangleRegularPoint → ℍ)) hg hf (1 : ℂ)
  rw [HolomorphicDifferentialForms.mfderiv_openSubtypeVal] at h
  exact h.trans rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
