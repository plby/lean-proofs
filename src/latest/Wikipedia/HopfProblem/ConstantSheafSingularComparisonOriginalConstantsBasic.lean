import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveBasic
import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyConstantBasic

/-!
# Units for the original and native additive constant sheaves

The existing comparison isomorphism forgets the ring structure of the
original constant complex sheaf and identifies it with Mathlib's native
constant additive sheaf.  Its action on the actual sheafification units is
the canonical one in both directions.  These statements retain the
original comparison isomorphism and all original presheaf maps.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.OriginalConstants

open CuspNormalization ConstantSheafFirstCohomology

/-- The original additive unit becomes the native constant-sheaf unit
under the canonical comparison isomorphism. -/
theorem additiveUnit_complexAdditiveSheafIso (X : TopCat.{0}) :
    SheafConstants.additiveUnit X ≫ (SheafConstants.complexAdditiveSheafIso X).hom.hom =
      Constant.unit X (AddCommGrpCat.of ℂ) := by
  change Functor.whiskerRight
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (CommRingCat.of ℂ)))
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ≫
      ((sheafifyComposeIso (Opens.grothendieckTopology X)
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
        ((Functor.const (Opens X)ᵒᵖ).obj (CommRingCat.of ℂ))).inv ≫
        sheafifyMap (Opens.grothendieckTopology X)
          (Functor.constComp (Opens X)ᵒᵖ (CommRingCat.of ℂ)
            (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).hom) =
      toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of ℂ))
  rw [sheafComposeIso_inv_fac_assoc, ← toSheafify_naturality]
  ext U c
  rfl

/-- Pointwise, the original constant representative is sent to the same
constant representative in the native additive sheaf. -/
@[simp]
theorem complexAdditiveSheafIso_app_unit (X : TopCat.{0}) (U : Opens X) (c : ℂ) :
    (SheafConstants.complexAdditiveSheafIso X).hom.hom.app (op U)
        ((SheafConstants.additiveUnit X).app (op U) c) =
      (Constant.unit X (AddCommGrpCat.of ℂ)).app (op U) c :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (additiveUnit_complexAdditiveSheafIso X) (op U)) c

/-- The inverse comparison also preserves the actual constant-sheaf unit. -/
theorem unit_complexAdditiveSheafIso_inv (X : TopCat.{0}) :
    Constant.unit X (AddCommGrpCat.of ℂ) ≫
        (SheafConstants.complexAdditiveSheafIso X).inv.hom =
      SheafConstants.additiveUnit X :=
  (Iso.comp_inv_eq
    ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso
      (SheafConstants.complexAdditiveSheafIso X))).mpr
    (additiveUnit_complexAdditiveSheafIso X).symm

/-- Pointwise, the inverse comparison returns the original constant
representative without changing its value. -/
@[simp]
theorem complexAdditiveSheafIso_inv_app_unit (X : TopCat.{0}) (U : Opens X) (c : ℂ) :
    (SheafConstants.complexAdditiveSheafIso X).inv.hom.app (op U)
        ((Constant.unit X (AddCommGrpCat.of ℂ)).app (op U) c) =
      (SheafConstants.additiveUnit X).app (op U) c :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (unit_complexAdditiveSheafIso_inv X) (op U)) c

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.OriginalConstants
