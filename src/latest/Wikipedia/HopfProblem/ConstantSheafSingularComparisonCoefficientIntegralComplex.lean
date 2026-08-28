import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCoefficientGlobal
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainIntegral
import Mathlib.Data.Complex.Basic

/-!
# The original integral cochains and the actual coefficient map to complex numbers

The source is the repository's original integer-linear singular cochain
complex, with only its scalar structure forgotten.  The coefficient map
takes each original integer value to that same integer in `ℂ`; no tensor
description or cohomology comparison is assumed.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

/-- The literal additive coefficient inclusion of integers into complex numbers. -/
def integerToComplexCoefficient : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℂ :=
  AddCommGrpCat.ofHom (Int.castAddHom ℂ)

@[simp]
theorem integerToComplexCoefficient_apply (z : ℤ) :
    integerToComplexCoefficient z = (z : ℂ) := rfl

/-- The actual coefficient map from the original integral singular cochains. -/
def integralToComplexCochainMap (X : Type) [TopologicalSpace X] :
    forgetIntegralCochains.obj (SingularCohomologyFree.singularCochainComplex X) ⟶
      singularCochainComplex X (AddCommGrpCat.of ℂ) :=
  (integralCochainIso X).inv ≫ coefficientMap X integerToComplexCoefficient

@[simp]
theorem integralToComplexCochainMap_apply (X : Type) [TopologicalSpace X] (n : ℕ)
    (φ : Chains X n →ₗ[ℤ] ℤ) (c : Chains X n) :
    (integralToComplexCochainMap X).f n φ c = (φ c : ℂ) := rfl

/-- The actual coefficient map is natural for the original continuous-map pullbacks. -/
@[reassoc]
theorem integralToComplexCochainMap_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    forgetIntegralCochains.map (SingularCohomologyFree.singularPullback f) ≫
        integralToComplexCochainMap X =
      integralToComplexCochainMap Y ≫ singularPullback (AddCommGrpCat.of ℂ) f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  ext φ c
  rfl

/-- The native global comparison with the repository's original integral source. -/
def integralGlobalCochainComparison (X : TopCat.{0}) :
    forgetIntegralCochains.obj (SingularCohomologyFree.singularCochainComplex X) ⟶
      globalSheafCochainComplex X (AddCommGrpCat.of ℤ) :=
  (integralCochainIso X).inv ≫ globalCochainComparison X (AddCommGrpCat.of ℤ)

/-- The global comparison preserves the literal coefficient map `ℤ → ℂ`,
including when the integral source is the original native cochain complex. -/
@[reassoc]
theorem integralGlobalCochainComparison_toComplex (X : TopCat.{0}) :
    integralGlobalCochainComparison X ≫
        globalSheafCoefficientMap X integerToComplexCoefficient =
      integralToComplexCochainMap X ≫
        globalCochainComparison X (AddCommGrpCat.of ℂ) := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (integralCochainIso X).inv ≫ f)
      (globalCochainComparison_coefficient_naturality X integerToComplexCoefficient)).trans
        (Category.assoc _ _ _).symm)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
