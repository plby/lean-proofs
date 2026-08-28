import Wikipedia.HopfProblem.SheafSingularCupComparisonSingularCup
import Wikipedia.HopfProblem.SheafSingularCupComparisonSingularIntegralClasses
import Wikipedia.HopfProblem.SingularCohomologyCupClasses

/-!
# Integral-to-complex compatibility of the original AW products

Both products use the original singular-simplex faces. Casting the
original integer-valued product therefore gives the complex-valued
product on cochains and on the original categorical cohomology groups.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.Singular

open FirstHurewicz ConstantSheafSingularComparison

theorem integral_frontFace :
    SingularCohomologyCup.frontFace 1 1 = simplexFace 1 2 := by
  change SingularCohomologyCup.vertexMap _ = SingularCohomologyCup.vertexMap _
  apply congrArg SingularCohomologyCup.vertexMap
  funext i
  fin_cases i <;> rfl

theorem integral_backFace :
    SingularCohomologyCup.backFace 1 1 = simplexFace 1 0 := by
  change SingularCohomologyCup.vertexMap _ = SingularCohomologyCup.vertexMap _
  apply congrArg SingularCohomologyCup.vertexMap
  funext i
  fin_cases i <;> rfl

variable (X : Type) [TopologicalSpace X]

/-- The original integral AW cochain maps to the actual complex-valued AW cochain. -/
theorem integralToComplex_cupCochain (a b : SingularCohomologyCup.Cochain X 1) :
    (integralToComplexCochainMap X).f 2 (SingularCohomologyCup.cup a b) =
      cupCochain X ℂ ((integralToComplexCochainMap X).f 1 a)
        ((integralToComplexCochainMap X).f 1 b) := by
  apply cochain_ext X (AddCommGrpCat.of ℂ) 2
  intro σ
  rw [cupCochain_simplex]
  change (SingularCohomologyCup.cup a b (simplexChain X 2 σ) : ℂ) =
    (a (simplexChain X 1 (σ.comp (simplexFace 1 2))) : ℂ) *
      (b (simplexChain X 1 (σ.comp (simplexFace 1 0))) : ℂ)
  rw [SingularCohomologyCup.cup_simplex, integral_frontFace, integral_backFace, Int.cast_mul]

/-- The genuine coefficient map preserves the original AW cocycle representative. -/
theorem integralToComplexCocycle_cup
    (a b : SingularCohomologyFree.Cocycle
      (SingularCohomologyFree.singularCochainComplex X) 1) :
    integralToComplexCocycle X 2 (SingularCohomologyCup.cupCocycles X 1 1 a b) =
      cupCocycle X ℂ (integralToComplexCocycle X 1 a) (integralToComplexCocycle X 1 b) := by
  apply Subtype.ext
  change (integralToComplexCochainMap X).f 2 (SingularCohomologyCup.cup a.val b.val) =
    cupCochain X ℂ ((integralToComplexCochainMap X).f 1 a.val)
      ((integralToComplexCochainMap X).f 1 b.val)
  exact integralToComplex_cupCochain X a.val b.val

/-- The already defined integral-to-complex map preserves the original native cup product. -/
theorem integralToComplex_cupProduct
    (a b : SingularCohomologyFree.SingularCohomology X 1) :
    integralToComplexCohomologyHom X 2 (SingularCohomologyCup.cupProduct X 1 1 a b) =
      cupProduct X (integralToComplexCohomologyHom X 1 a)
        (integralToComplexCohomologyHom X 1 b) := by
  obtain ⟨a, rfl⟩ := SingularCohomologyFree.cocycleClass_surjective
    (SingularCohomologyFree.singularCochainComplex X) 1 a
  obtain ⟨b, rfl⟩ := SingularCohomologyFree.cocycleClass_surjective
    (SingularCohomologyFree.singularCochainComplex X) 1 b
  rw [SingularCohomologyCup.cupProduct_cocycleClass,
    integralToComplexCohomologyHom_class, integralToComplexCohomologyHom_class,
    integralToComplexCohomologyHom_class, cupProduct_class, integralToComplexCocycle_cup]

end Wikipedia.HopfProblem.SheafSingularCupComparison.Singular
