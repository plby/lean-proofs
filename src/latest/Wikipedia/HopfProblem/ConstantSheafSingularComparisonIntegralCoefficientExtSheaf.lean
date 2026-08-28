import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCoefficientIntegralComplex
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonOriginalConstantsBasic
import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyComplex

/-!
# The literal integer coefficient map to the original complex sheaf

The map is the native constant-sheaf map for `ℤ → ℂ`, followed by the
inverse of the original constant-ring/additive-sheaf comparison.  On the
actual sheafification units it sends an integer to that same integer as
a complex number.  The corresponding native Ext map is compatible with
the original sheaf comparison in every degree.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open CuspNormalization.SheafConstants

variable (X : TopCat.{0})

/-- The canonical coefficient inclusion into the manuscript's original
constant complex sheaf. -/
def integerToOriginalComplexSheafMap :
    ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℤ) ⟶
      complexAdditiveSheaf X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{0}).map integerToComplexCoefficient ≫ (complexAdditiveSheafIso X).inv

/-- The sheafification unit witnesses the literal coefficient map. -/
@[reassoc]
theorem integerToOriginalComplexSheafMap_unit :
    ConstantSheafFirstCohomology.Constant.unit X (AddCommGrpCat.of ℤ) ≫
        (integerToOriginalComplexSheafMap X).hom =
      constantPresheafCoefficientMap X integerToComplexCoefficient ≫ additiveUnit X := by
  change ConstantSheafFirstCohomology.Constant.unit X (AddCommGrpCat.of ℤ) ≫
      (((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{0}).map integerToComplexCoefficient).hom ≫
        (complexAdditiveSheafIso X).inv.hom) = _
  let u := ConstantSheafFirstCohomology.Constant.unit X (AddCommGrpCat.of ℤ)
  let a : (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℤ)).obj ⟶
      (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℂ)).obj :=
    ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).map integerToComplexCoefficient).hom
  let v : (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℂ)).obj ⟶
      (complexAdditiveSheaf X).obj := (complexAdditiveSheafIso X).inv.hom
  let b := constantPresheafCoefficientMap X integerToComplexCoefficient
  let w := ConstantSheafFirstCohomology.Constant.unit X (AddCommGrpCat.of ℂ)
  exact (Category.assoc u a v).symm.trans
    ((congrArg (fun f => f ≫ v) (constantUnit_coefficient_naturality X
      integerToComplexCoefficient)).trans
        ((Category.assoc b w v).trans
          (congrArg (fun f => b ≫ f) (OriginalConstants.unit_complexAdditiveSheafIso_inv X))))

/-- An integer constant section is sent to that same complex constant
section in the original ring-sheafification model. -/
@[simp]
theorem integerToOriginalComplexSheafMap_app_unit (U : Opens X) (z : ℤ) :
    (integerToOriginalComplexSheafMap X).hom.app (op U)
        ((ConstantSheafFirstCohomology.Constant.unit X (AddCommGrpCat.of ℤ)).app (op U) z) =
      (additiveUnit X).app (op U) (z : ℂ) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (integerToOriginalComplexSheafMap_unit X) (op U)) z

/-- Composing with the original sheaf comparison returns exactly
Mathlib's native constant-sheaf coefficient map. -/
@[reassoc]
theorem integerToOriginalComplexSheafMap_comparison :
    integerToOriginalComplexSheafMap X ≫ (complexAdditiveSheafIso X).hom =
      (CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{0}).map integerToComplexCoefficient := by
  let a : ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℤ) ⟶
      ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℂ) :=
    (CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).map integerToComplexCoefficient
  let e := complexAdditiveSheafIso X
  exact (Category.assoc a e.inv e.hom).trans
    ((congrArg (fun f => a ≫ f) e.inv_hom_id).trans (Category.comp_id a))

/-- The original complex-sheaf coefficient map has the actual native
constant-sheaf Ext map as its comparison in every degree. -/
@[reassoc]
theorem integerToOriginalComplexSheafMap_cohomology_comparison (n : ℕ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).map
        (integerToOriginalComplexSheafMap X) ≫
      (ConstantSheafFirstCohomology.complexConstantCohomologyEquiv X n).toAddCommGrpIso.hom =
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).map
      ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{0}).map integerToComplexCoefficient) := by
  change (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).map
      (integerToOriginalComplexSheafMap X) ≫
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).map
      (complexAdditiveSheafIso X).hom = _
  let F := CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n
  exact (F.map_comp (integerToOriginalComplexSheafMap X)
    (complexAdditiveSheafIso X).hom).symm.trans
      (congrArg F.map (integerToOriginalComplexSheafMap_comparison X))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
