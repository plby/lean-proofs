import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyBaseFunctionActionCocycle

/-!
# The native holomorphic base-module structure on period-family cohomology

The actual sheaf cohomology functor sends the proved base-multiplier
ring homomorphism to its action on the original native cohomology groups.
This defines the holomorphic base-module structure without transporting
it from another group. The original complex action is unchanged, and
the actual period-class map is linear over actual holomorphic functions.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.BaseFunctionAction

open PeriodFamilyHigherDirectImage CuspNormalization.SheafCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The original cohomology functor applied to the genuine coefficient
endomorphisms gives the actual ring action on each native cohomology group. -/
def baseCohomologyEnd (P : HolomorphicPeriodMap V B) (q : ℕ) :
    BaseFunction V B →+*
      End ((CategoryTheory.Sheaf.functorH _ q).obj (Zero.totalAdditiveSheaf P)) :=
  (mapEndRingHom (CategoryTheory.Sheaf.functorH _ q) (Zero.totalAdditiveSheaf P)).comp
    (baseMultiplyRingHom P)

/-- Actual holomorphic base functions act on the original native cohomology
through their literal coefficient sheaf endomorphisms. -/
@[instance_reducible] def baseCohomologyModule (P : HolomorphicPeriodMap V B) (q : ℕ) :
    Module (BaseFunction V B) (CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q) :=
  moduleOfScalarEnd ((CategoryTheory.Sheaf.functorH _ q).obj (Zero.totalAdditiveSheaf P))
    (baseCohomologyEnd P q)

/-- The native module action is exactly the original cohomology map. -/
theorem baseCohomologyModule_smul (P : HolomorphicPeriodMap V B) (q : ℕ)
    (g : BaseFunction V B) (x : CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q) :
    letI := baseCohomologyModule P q
    g • x = CategoryTheory.Sheaf.H.map (baseMultiplyEnd P g) q x := rfl

/-- The genuine holomorphic base action recovers the unchanged original
complex scalar action on native cohomology. -/
theorem baseCohomologyModule_algebraMap_smul (P : HolomorphicPeriodMap V B) (q : ℕ)
    (c : ℂ) (x : CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q) :
    letI := Cocycle.totalCohomologyModule P q
    letI := baseCohomologyModule P q
    algebraMap ℂ (BaseFunction V B) c • x = c • x := by
  let := Cocycle.totalCohomologyModule P q
  let := baseCohomologyModule P q
  change CategoryTheory.Sheaf.H.map
    (baseMultiplyEnd P (algebraMap ℂ (BaseFunction V B) c)) q x =
      CategoryTheory.Sheaf.H.map (Zero.totalScalarEnd P c) q x
  rw [baseMultiplyEnd_algebraMap]

/-- The two original actions form the actual complex/holomorphic-base scalar tower. -/
theorem baseCohomologyScalarTower (P : HolomorphicPeriodMap V B) (q : ℕ) :
    letI := Cocycle.totalCohomologyModule P q
    letI := baseCohomologyModule P q
    IsScalarTower ℂ (BaseFunction V B)
      (CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) q) := by
  let := Cocycle.totalCohomologyModule P q
  let := baseCohomologyModule P q
  exact IsScalarTower.of_algebraMap_smul (baseCohomologyModule_algebraMap_smul P q)

/-- The period-class map respects the actual holomorphic base-module action. -/
theorem periodClass_base_smul (P : HolomorphicPeriodMap V B) (g : BaseFunction V B)
    (a : Cocycle.Coefficients V B) :
    letI := baseCohomologyModule P 1
    Cocycle.periodClass P (g • a) = g • Cocycle.periodClass P a :=
  periodClass_mul_base P g a

/-- The original period-class map is linear over genuine holomorphic
base functions, with the original coefficient-induced target action. -/
def periodClassBaseLinearMap (P : HolomorphicPeriodMap V B) :
    letI := baseCohomologyModule P 1
    Cocycle.Coefficients V B →ₗ[BaseFunction V B]
      CategoryTheory.Sheaf.H.{0} (Zero.totalAdditiveSheaf P) 1 := by
  letI := baseCohomologyModule P 1
  exact { Cocycle.periodClassHom P with map_smul' := periodClass_base_smul P }

@[simp] theorem periodClassBaseLinearMap_apply (P : HolomorphicPeriodMap V B)
    (a : Cocycle.Coefficients V B) :
    letI := baseCohomologyModule P 1
    periodClassBaseLinearMap P a = Cocycle.periodClass P a := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.BaseFunctionAction
