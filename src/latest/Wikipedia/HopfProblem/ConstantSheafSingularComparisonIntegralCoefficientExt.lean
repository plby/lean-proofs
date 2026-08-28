import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCoefficientExt
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonConcreteCoefficients
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonIntegralCoefficientExtCohomology
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonIntegralCoefficientExtSheaf

/-!
# Original integral and complex comparisons respect the coefficient inclusion

The source singular cohomology is the repository's original integer-linear
cohomology.  The target sheaf is the manuscript's original constant
complex sheaf.  The comparison squares use only the literal `ℤ → ℂ`
cochain map and the canonical constant-sheaf map.  No tensor-product or
cohomological base-change assertion is assumed.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : TopCat.{0}) [CompactSpace X] [T2Space X]

/-- The original integral H¹ endpoint commutes with the literal
coefficient inclusion and native constant-complex-sheaf cohomology. -/
@[reassoc]
theorem integralSheafH1Iso_toComplex (hLC : LocallyContractibleSpace X) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1).map
        ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{0}).map integerToComplexCoefficient) ≫
        (constantSheafH1Iso X (AddCommGrpCat.of ℂ) hLC).hom =
      (integralSheafH1Iso X hLC).hom ≫ integralToComplexCohomologyMap X 1 := by
  rw [constantSheafH1Iso_coefficient_naturality]
  change _ = ((constantSheafH1Iso X (AddCommGrpCat.of ℤ) hLC).hom ≫
    (integralCohomologyIso X 1).hom) ≫ integralToComplexCohomologyMap X 1
  rw [Category.assoc, integralCohomologyIso_toComplex]

/-- The same genuine coefficient comparison in degree two. -/
@[reassoc]
theorem integralSheafH2Iso_toComplex (hLC : LocallyContractibleSpace X) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2).map
        ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{0}).map integerToComplexCoefficient) ≫
        (constantSheafH2Iso X (AddCommGrpCat.of ℂ) hLC).hom =
      (integralSheafH2Iso X hLC).hom ≫ integralToComplexCohomologyMap X 2 := by
  rw [constantSheafH2Iso_coefficient_naturality]
  change _ = ((constantSheafH2Iso X (AddCommGrpCat.of ℤ) hLC).hom ≫
    (integralCohomologyIso X 2).hom) ≫ integralToComplexCohomologyMap X 2
  rw [Category.assoc, integralCohomologyIso_toComplex]

/-- Both ends of the H¹ square use the original objects: the
integer-linear singular cohomology and the constant complex ring sheaf
with only its additive structure retained. -/
@[reassoc]
theorem integralSheafH1Iso_toOriginalComplex (hLC : LocallyContractibleSpace X) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1).map
        (integerToOriginalComplexSheafMap X) ≫ (complexSheafH1Iso X hLC).hom =
      (integralSheafH1Iso X hLC).hom ≫ integralToComplexCohomologyMap X 1 := by
  let a : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℤ)) 1) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (CuspNormalization.SheafConstants.complexAdditiveSheaf X) 1) :=
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1).map
      (integerToOriginalComplexSheafMap X)
  let e : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (CuspNormalization.SheafConstants.complexAdditiveSheaf X) 1) ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℂ)) 1) :=
    (ConstantSheafFirstCohomology.complexConstantCohomologyEquiv X 1).toAddCommGrpIso
  let c := (constantSheafH1Iso X (AddCommGrpCat.of ℂ) hLC).hom
  exact (Category.assoc a e.hom c).symm.trans
    ((congrArg (fun f => f ≫ c)
      (integerToOriginalComplexSheafMap_cohomology_comparison X 1)).trans
        (integralSheafH1Iso_toComplex X hLC))

/-- The original-object H² comparison respects the same actual
coefficient inclusion. -/
@[reassoc]
theorem integralSheafH2Iso_toOriginalComplex (hLC : LocallyContractibleSpace X) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2).map
        (integerToOriginalComplexSheafMap X) ≫ (complexSheafH2Iso X hLC).hom =
      (integralSheafH2Iso X hLC).hom ≫ integralToComplexCohomologyMap X 2 := by
  let a : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℤ)) 2) ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (CuspNormalization.SheafConstants.complexAdditiveSheaf X) 2) :=
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2).map
      (integerToOriginalComplexSheafMap X)
  let e : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (CuspNormalization.SheafConstants.complexAdditiveSheaf X) 2) ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
        (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℂ)) 2) :=
    (ConstantSheafFirstCohomology.complexConstantCohomologyEquiv X 2).toAddCommGrpIso
  let c := (constantSheafH2Iso X (AddCommGrpCat.of ℂ) hLC).hom
  exact (Category.assoc a e.hom c).symm.trans
    ((congrArg (fun f => f ≫ c)
      (integerToOriginalComplexSheafMap_cohomology_comparison X 2)).trans
        (integralSheafH2Iso_toComplex X hLC))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
