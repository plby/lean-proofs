import Wikipedia.HopfProblem.SheafSingularCupComparisonRowGlobalBasic

/-!
# The actual singular-cochain unit on original cohomology classes

These maps come from the actual ring sheafification unit and the proved
native singular-cohomology comparison with its original coface quotient.
The coface morphism proves preservation of the literal AW product.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal

open RingCochains ConstantSheafSingularComparison

variable (X : TopCat.{0})

/-- The actual ring-cochain unit on original singular H¹. -/
def unitOne :
    (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1 →+
      (globalData X).CohomologyOne :=
  (globalUnitMorphism X).cohomologyOneMap.comp
    (Singular.oneHomologyEquiv X ℂ).toAddMonoidHom

/-- The actual ring-cochain unit on original singular H². -/
def unitTwo :
    (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 2 →+
      (globalData X).CohomologyTwo :=
  (globalUnitMorphism X).cohomologyTwoMap.comp
    (Singular.twoHomologyEquiv X ℂ).toAddMonoidHom

/-- The first unit map keeps the actual original singular cocycle. -/
theorem unitOne_class (a : Singular.Cocycle X ℂ 1) :
    unitOne X (Singular.classMap X ℂ 1 a) =
      (globalData X).classOne
        ((globalUnitMorphism X).cocycleOneMap (Singular.oneCocycleEvaluation X ℂ a)) := by
  change (globalUnitMorphism X).cohomologyOneMap
    (Singular.oneHomologyEquiv X ℂ (Singular.classMap X ℂ 1 a)) = _
  rw [Singular.oneHomologyEquiv_class,
    SheafCupProduct.Coface.Data.Morphism.cohomologyOneMap_classOne]

/-- The second unit map keeps the actual original singular cocycle. -/
theorem unitTwo_class (a : Singular.Cocycle X ℂ 2) :
    unitTwo X (Singular.classMap X ℂ 2 a) =
      (globalData X).classTwo
        ((globalUnitMorphism X).cocycleTwoMap (Singular.twoCocycleEvaluation X ℂ a)) := by
  change (globalUnitMorphism X).cohomologyTwoMap
    (Singular.twoHomologyEquiv X ℂ (Singular.classMap X ℂ 2 a)) = _
  rw [Singular.twoHomologyEquiv_class,
    SheafCupProduct.Coface.Data.Morphism.cohomologyTwoMap_classTwo]

/-- The actual unit-induced maps preserve the original singular AW cup product. -/
theorem unit_cup
    (a b : (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1) :
    unitTwo X (Singular.cupProduct X a b) =
      (globalData X).cup (unitOne X a) (unitOne X b) := by
  change (globalUnitMorphism X).cohomologyTwoMap
    (Singular.twoHomologyEquiv X ℂ (Singular.ringCupProduct X ℂ a b)) = _
  rw [Singular.ringCupProduct_comparison]
  exact (globalUnitMorphism X).map_cup _ _

end Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal
