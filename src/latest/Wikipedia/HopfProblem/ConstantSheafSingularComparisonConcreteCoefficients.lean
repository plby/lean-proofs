import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowDegrees
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainIntegralCohomology
import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyComplex

/-!
# The original complex and integral coefficient endpoints

The complex comparison starts with the additive sheaf underlying the
manuscript's original constant complex ring sheaf.  The integral
comparison ends with the previously constructed integer-linear singular
cohomology, not a newly chosen cohomology group.  Both comparisons use
the canonical isomorphisms of the original sheaves and cochain complexes.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open CuspNormalization.SheafConstants

variable (X : TopCat.{0}) [CompactSpace X] [T2Space X]

/-- Genuine Ext H¹ of the original constant complex sheaf is the
cohomology of the actual complex-valued singular cochains. -/
def complexSheafH1Iso (hLC : LocallyContractibleSpace X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 1) ≅
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1 :=
  (ConstantSheafFirstCohomology.complexConstantCohomologyEquiv X 1).toAddCommGrpIso ≪≫
    constantSheafH1Iso X (AddCommGrpCat.of ℂ) hLC

/-- The same comparison in degree two, for the original complex sheaf. -/
def complexSheafH2Iso (hLC : LocallyContractibleSpace X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 2) ≅
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 2 :=
  (ConstantSheafFirstCohomology.complexConstantCohomologyEquiv X 2).toAddCommGrpIso ≪≫
    constantSheafH2Iso X (AddCommGrpCat.of ℂ) hLC

/-- The original complex-coefficient comparison as an additive equivalence. -/
def complexSheafH1Equiv (hLC : LocallyContractibleSpace X) :
    CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 1 ≃+
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1 :=
  (complexSheafH1Iso X hLC).addCommGroupIsoToAddEquiv

/-- The original complex-coefficient comparison in degree two. -/
def complexSheafH2Equiv (hLC : LocallyContractibleSpace X) :
    CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 2 ≃+
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 2 :=
  (complexSheafH2Iso X hLC).addCommGroupIsoToAddEquiv

/-- The forward map uses exactly the cohomology map of the original
constant-ring/additive-sheaf comparison. -/
theorem complexSheafH1Equiv_apply (hLC : LocallyContractibleSpace X)
    (ξ : CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 1) :
    complexSheafH1Equiv X hLC ξ =
      (constantSheafH1Iso X (AddCommGrpCat.of ℂ) hLC).hom
        (CategoryTheory.Sheaf.H.map.{0} (complexAdditiveSheafIso X).hom 1 ξ) := rfl

/-- The same literal induced-map characterization in degree two. -/
theorem complexSheafH2Equiv_apply (hLC : LocallyContractibleSpace X)
    (ξ : CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 2) :
    complexSheafH2Equiv X hLC ξ =
      (constantSheafH2Iso X (AddCommGrpCat.of ℂ) hLC).hom
        (CategoryTheory.Sheaf.H.map.{0} (complexAdditiveSheafIso X).hom 2 ξ) := rfl

/-- Genuine constant-integer-sheaf Ext H¹ agrees with the original
integer-linear singular cohomology, after forgetting only its scalars. -/
def integralSheafH1Iso (hLC : LocallyContractibleSpace X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℤ)) 1) ≅
        integralForget.obj (SingularCohomologyFree.SingularCohomology X 1) :=
  constantSheafH1Iso X (AddCommGrpCat.of ℤ) hLC ≪≫ integralCohomologyIso X 1

/-- The same original integer-coefficient comparison in degree two. -/
def integralSheafH2Iso (hLC : LocallyContractibleSpace X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℤ)) 2) ≅
        integralForget.obj (SingularCohomologyFree.SingularCohomology X 2) :=
  constantSheafH2Iso X (AddCommGrpCat.of ℤ) hLC ≪≫ integralCohomologyIso X 2

/-- The integral comparison has the original singular cohomology group
as its literal target type. -/
def integralSheafH1Equiv (hLC : LocallyContractibleSpace X) :
    CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℤ)) 1 ≃+
        SingularCohomologyFree.SingularCohomology X 1 :=
  (integralSheafH1Iso X hLC).addCommGroupIsoToAddEquiv

/-- The original degree-two integral comparison as an additive equivalence. -/
def integralSheafH2Equiv (hLC : LocallyContractibleSpace X) :
    CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℤ)) 2 ≃+
        SingularCohomologyFree.SingularCohomology X 2 :=
  (integralSheafH2Iso X hLC).addCommGroupIsoToAddEquiv

/-- The forward integral comparison is the actual coefficient-general
comparison followed by the original integer-cochain comparison. -/
theorem integralSheafH1Equiv_apply (hLC : LocallyContractibleSpace X)
    (ξ : CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℤ)) 1) :
    integralSheafH1Equiv X hLC ξ =
      integralCohomologyEquiv X 1
        ((constantSheafH1Iso X (AddCommGrpCat.of ℤ) hLC).hom ξ) := rfl

/-- The same actual-comparison characterization in degree two. -/
theorem integralSheafH2Equiv_apply (hLC : LocallyContractibleSpace X)
    (ξ : CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℤ)) 2) :
    integralSheafH2Equiv X hLC ξ =
      integralCohomologyEquiv X 2
        ((constantSheafH2Iso X (AddCommGrpCat.of ℤ) hLC).hom ξ) := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
