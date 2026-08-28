import Wikipedia.HopfProblem.ConstantSheafSingularComparisonOriginalConstantsBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveMaps

/-!
# The original complex constant maps agree with native constant pullback

The constant complex sheaf used in the normalization sequence was first
constructed as a ring sheaf and then regarded as an additive sheaf. Its
original comparison with the native additive constant sheaf preserves
the actual constant representatives. Consequently its original pullback
map agrees, under that same comparison, with the native constant map
used in the singular-cochain resolution.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.OriginalConstants

open CuspNormalization ConstantSheafFirstCohomology

variable {X Y : TopCat.{0}}

/-- Maps from the original ring-forgotten complex constant sheaf are
determined by their values on the original constant representatives. -/
theorem additive_hom_ext {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {a b : SheafConstants.complexAdditiveSheaf X ⟶ F}
    (h : SheafConstants.additiveUnit X ≫ a.hom =
      SheafConstants.additiveUnit X ≫ b.hom) : a = b := by
  apply (Iso.cancel_iso_hom_left (SheafConstants.complexAdditiveSheafIso X).symm a b).mp
  apply Constant.hom_ext
  change Constant.unit X (AddCommGrpCat.of ℂ) ≫
      ((SheafConstants.complexAdditiveSheafIso X).inv.hom ≫ a.hom) =
    Constant.unit X (AddCommGrpCat.of ℂ) ≫
      ((SheafConstants.complexAdditiveSheafIso X).inv.hom ≫ b.hom)
  have hcomp (g : SheafConstants.complexAdditiveSheaf X ⟶ F) :
      Constant.unit X (AddCommGrpCat.of ℂ) ≫
          ((SheafConstants.complexAdditiveSheafIso X).inv.hom ≫ g.hom) =
        SheafConstants.additiveUnit X ≫ g.hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ g.hom) (unit_complexAdditiveSheafIso_inv X))
  exact (hcomp a).trans (h.trans (hcomp b).symm)

/-- The literal ring-forgotten pullback is carried to the native
constant pullback by the original additive sheafification comparison. -/
@[reassoc]
theorem additivePullbackMap_complexAdditiveSheafIso (f : X ⟶ Y) :
    SheafConstants.additivePullbackMap f ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat f).map
          (SheafConstants.complexAdditiveSheafIso X).hom =
      (SheafConstants.complexAdditiveSheafIso Y).hom ≫
        PullbackSheaf.constantPullback f (AddCommGrpCat.of ℂ) := by
  apply additive_hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  change (SheafConstants.complexAdditiveSheafIso X).hom.hom.app
      (op ((Opens.map f).obj U.unop))
      ((SheafConstants.additivePullbackMap f).hom.app U
        ((SheafConstants.additiveUnit Y).app U c)) =
    (PullbackSheaf.constantPullback f (AddCommGrpCat.of ℂ)).hom.app U
      ((SheafConstants.complexAdditiveSheafIso Y).hom.hom.app U
        ((SheafConstants.additiveUnit Y).app U c))
  exact (congrArg ((SheafConstants.complexAdditiveSheafIso X).hom.hom.app
      (op ((Opens.map f).obj U.unop)))
      (SheafConstants.additivePullbackMap_unit f U.unop c)).trans
    ((complexAdditiveSheafIso_app_unit X ((Opens.map f).obj U.unop) c).trans
      ((PullbackSheaf.constantPullback_app_unit f (AddCommGrpCat.of ℂ) U.unop c).symm.trans
        (congrArg ((PullbackSheaf.constantPullback f (AddCommGrpCat.of ℂ)).hom.app U)
          (complexAdditiveSheafIso_app_unit Y U.unop c).symm)))

/-- An explicit equality expressing the original constant map through
the same native constant map and the original comparison isomorphisms. -/
theorem additivePullbackMap_eq (f : X ⟶ Y) :
    SheafConstants.additivePullbackMap f =
      (SheafConstants.complexAdditiveSheafIso Y).hom ≫
        PullbackSheaf.constantPullback f (AddCommGrpCat.of ℂ) ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat f).map
            (SheafConstants.complexAdditiveSheafIso X).inv := by
  exact ((Iso.eq_comp_inv
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).mapIso
        (SheafConstants.complexAdditiveSheafIso X))).mpr
      (additivePullbackMap_complexAdditiveSheafIso f)).trans
    (Category.assoc _ _ _)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.OriginalConstants
