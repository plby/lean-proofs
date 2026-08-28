import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLinearComparisonBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCoefficientExt
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonConcreteCoefficients
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonOriginalConstantsScalar

/-!
# The original comparison intertwines actual complex scalar maps

The scalar map on the original constant sheaf is multiplication by its
actual constant sections. The singular scalar map is induced by literal
coefficient multiplication on the original singular cochains. The
canonical comparison intertwines these maps in degrees one and two.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open CuspNormalization.SheafConstants

/-- The original/native constant-sheaf cohomology comparison respects
the actual scalar map in every degree. -/
@[reassoc]
theorem complexConstantCohomology_scalar_naturality (X : TopCat.{0}) (n : ℕ) (c : ℂ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).map
        (SheafCupProduct.constantScalarEnd X c).asHom ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).map
        (complexAdditiveSheafIso X).hom =
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).map
        (complexAdditiveSheafIso X).hom ≫
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).map
        ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
          (OriginalConstants.complexScalarCoefficient c)) := by
  let F := CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n
  let a := (SheafCupProduct.constantScalarEnd X c).asHom
  let e := complexAdditiveSheafIso X
  let b := (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
    (OriginalConstants.complexScalarCoefficient c)
  exact (F.map_comp a e.hom).symm.trans
    ((congrArg F.map (OriginalConstants.constantScalarEnd_complexAdditiveSheafIso X c)).trans
      (F.map_comp e.hom b))

variable (X : TopCat.{0}) [CompactSpace X] [T2Space X]

/-- The original H¹ comparison intertwines the original sheaf scalar
action with literal coefficient multiplication on singular cohomology. -/
@[reassoc]
theorem complexSheafH1Iso_scalar_naturality (hLC : LocallyContractibleSpace X) (c : ℂ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1).map
        (SheafCupProduct.constantScalarEnd X c).asHom ≫ (complexSheafH1Iso X hLC).hom =
      (complexSheafH1Iso X hLC).hom ≫
        HomologicalComplex.homologyMap
          (coefficientMap X (OriginalConstants.complexScalarCoefficient c)) 1 := by
  let F := CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1
  let S : AddCommGrpCat := F.obj (complexAdditiveSheaf X)
  let M : AddCommGrpCat :=
    F.obj (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℂ))
  let T : AddCommGrpCat := (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1
  let a : S ⟶ S := F.map (SheafCupProduct.constantScalarEnd X c).asHom
  let b : M ⟶ M := F.map
    ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      (OriginalConstants.complexScalarCoefficient c))
  let d : T ⟶ T := HomologicalComplex.homologyMap
    (coefficientMap X (OriginalConstants.complexScalarCoefficient c)) 1
  let u : S ⟶ M := F.map (complexAdditiveSheafIso X).hom
  let v : M ⟶ T := (constantSheafH1Iso X (AddCommGrpCat.of ℂ) hLC).hom
  exact LinearComparison.comp_intertwines a b d u v
    (complexConstantCohomology_scalar_naturality X 1 c)
    (constantSheafH1Iso_coefficient_naturality X hLC (OriginalConstants.complexScalarCoefficient c))

/-- The same original scalar compatibility for the genuine degree-two
Ext--singular comparison. -/
@[reassoc]
theorem complexSheafH2Iso_scalar_naturality (hLC : LocallyContractibleSpace X) (c : ℂ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2).map
        (SheafCupProduct.constantScalarEnd X c).asHom ≫ (complexSheafH2Iso X hLC).hom =
      (complexSheafH2Iso X hLC).hom ≫
        HomologicalComplex.homologyMap
          (coefficientMap X (OriginalConstants.complexScalarCoefficient c)) 2 := by
  let F := CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2
  let S : AddCommGrpCat := F.obj (complexAdditiveSheaf X)
  let M : AddCommGrpCat :=
    F.obj (ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℂ))
  let T : AddCommGrpCat := (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 2
  let a : S ⟶ S := F.map (SheafCupProduct.constantScalarEnd X c).asHom
  let b : M ⟶ M := F.map
    ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      (OriginalConstants.complexScalarCoefficient c))
  let d : T ⟶ T := HomologicalComplex.homologyMap
    (coefficientMap X (OriginalConstants.complexScalarCoefficient c)) 2
  let u : S ⟶ M := F.map (complexAdditiveSheafIso X).hom
  let v : M ⟶ T := (constantSheafH2Iso X (AddCommGrpCat.of ℂ) hLC).hom
  exact LinearComparison.comp_intertwines a b d u v
    (complexConstantCohomology_scalar_naturality X 2 c)
    (constantSheafH2Iso_coefficient_naturality X hLC (OriginalConstants.complexScalarCoefficient c))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
