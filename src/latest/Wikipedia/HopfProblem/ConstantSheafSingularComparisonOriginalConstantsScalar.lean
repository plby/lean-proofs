import Wikipedia.HopfProblem.ConstantSheafSingularComparisonOriginalConstantsScalarBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonOriginalConstants
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCoefficientSheaf
import Wikipedia.HopfProblem.SheafCupProductCoefficients

/-!
# The original constant-sheaf comparison preserves actual complex scalars

The original scalar endomorphism multiplies sections by their literal
constant complex sections. On the original constant representatives it
therefore agrees with coefficient multiplication. The same comparison
isomorphism consequently intertwines the original scalar map with the
native constant-sheaf functor applied to that actual coefficient map.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.OriginalConstants

open CuspNormalization ConstantSheafFirstCohomology

/-- Original scalar multiplication sends each original constant section
to the section represented by the product of its complex coefficients. -/
@[simp]
theorem constantScalarEnd_app_unit (X : TopCat.{0}) (z : ℂ) (U : Opens X) (c : ℂ) :
    (SheafCupProduct.constantScalarEnd X z).hom.app (op U)
        ((SheafConstants.additiveUnit X).app (op U) c) =
      (SheafConstants.additiveUnit X).app (op U) (z * c) :=
  (SheafCupProduct.constantScalarEnd_apply X z (op U)
    ((SheafConstants.unit X).app (op U) c)).trans
      (((SheafConstants.unit X).app (op U)).hom.map_mul z c).symm

/-- The native constant-sheaf functor retains the literal coefficient
multiplication on each original sheafification-unit representative. -/
@[simp]
theorem nativeConstantScalar_app_unit (X : TopCat.{0}) (z : ℂ) (U : Opens X) (c : ℂ) :
    ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
        (complexScalarCoefficient z)).hom.app (op U)
        ((Constant.unit X (AddCommGrpCat.of ℂ)).app (op U) c) =
      (Constant.unit X (AddCommGrpCat.of ℂ)).app (op U) (z * c) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (constantUnit_coefficient_naturality X (complexScalarCoefficient z)) (op U)) c

/-- The existing additive comparison intertwines the original scalar
endomorphism with the native constant-sheaf map of coefficient multiplication. -/
@[reassoc]
theorem constantScalarEnd_complexAdditiveSheafIso (X : TopCat.{0}) (z : ℂ) :
    (SheafCupProduct.constantScalarEnd X z).asHom ≫
        (SheafConstants.complexAdditiveSheafIso X).hom =
      (SheafConstants.complexAdditiveSheafIso X).hom ≫
        (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
          (complexScalarCoefficient z) := by
  apply additive_hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  change ℂ at c
  change (SheafConstants.complexAdditiveSheafIso X).hom.hom.app U
      ((SheafCupProduct.constantScalarEnd X z).hom.app U
        ((SheafConstants.additiveUnit X).app U c)) =
    ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      (complexScalarCoefficient z)).hom.app U
      ((SheafConstants.complexAdditiveSheafIso X).hom.hom.app U
        ((SheafConstants.additiveUnit X).app U c))
  exact (congrArg ((SheafConstants.complexAdditiveSheafIso X).hom.hom.app U)
      (constantScalarEnd_app_unit X z U.unop c)).trans
    ((complexAdditiveSheafIso_app_unit X U.unop (z * c)).trans
      ((nativeConstantScalar_app_unit X z U.unop c).symm.trans
        (congrArg
          (((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
            (complexScalarCoefficient z)).hom.app U)
          (complexAdditiveSheafIso_app_unit X U.unop c).symm)))

/-- An equality with the actual original scalar endomorphism, using
the original comparison isomorphism and native coefficient map. -/
theorem constantScalarEnd_eq (X : TopCat.{0}) (z : ℂ) :
    (SheafCupProduct.constantScalarEnd X z).asHom =
      (SheafConstants.complexAdditiveSheafIso X).hom ≫
        (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
          (complexScalarCoefficient z) ≫
            (SheafConstants.complexAdditiveSheafIso X).inv :=
  ((Iso.eq_comp_inv (SheafConstants.complexAdditiveSheafIso X)).mpr
    (constantScalarEnd_complexAdditiveSheafIso X z)).trans (Category.assoc _ _ _)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.OriginalConstants
