import Wikipedia.HopfProblem.SheafSingularCupComparisonRingSheaf
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonOriginalConstants

/-!
# The original complex constant sheaf augments the ring cochains

The augmentation sends a literal constant to the constant function on
singular vertices and then applies native sheafification. Its forgotten
additive map agrees with the original constant-to-singular-cochain map,
under the original constant-sheaf and cochain-sheaf comparisons.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains

open FirstHurewicz ConstantSheafSingularComparison
open CuspNormalization
open CuspNormalization.SheafForgetStalk (forgetToAdd)

variable (X : TopCat.{0})

/-- Literal constants give the actual ring-valued zero-cochains. -/
def augmentationPresheaf : SheafConstants.constantPresheaf X ⟶ presheaf X 0 where
  app U := CommRingCat.ofHom
    { toFun := fun z _ => z
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality _ _ i := by ext z; rfl

@[simp] theorem augmentationPresheaf_apply (U : Opens X) (z : ℂ)
    (σ : SingularSimplex U 0) :
    (augmentationPresheaf X).app (op U) z σ = z := rfl

/-- The original additive augmentation is literally the basis extension of constants. -/
theorem augmentationPresheaf_additive :
    Functor.whiskerRight (augmentationPresheaf X) forgetToAdd ≫
        (presheafAddIso X 0).hom = constantAugmentation X (AddCommGrpCat.of ℂ) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  rfl

/-- The genuine original complex constant ring sheaf augments the ring cochains. -/
def augmentation : SheafConstants.complexSheaf X ⟶ sheaf X 0 :=
  (ringSheafification X).map (augmentationPresheaf X)

/-- The original constant representatives retain their literal cochain values. -/
@[reassoc] theorem unit_augmentation :
    SheafConstants.unit X ≫ (augmentation X).hom =
      augmentationPresheaf X ≫ unit X 0 :=
  (toSheafify_naturality (Opens.grothendieckTopology X) (augmentationPresheaf X)).symm

@[simp] theorem augmentation_app_unit (U : Opens X) (z : ℂ) :
    (augmentation X).hom.app (op U) ((SheafConstants.unit X).app (op U) z) =
      (unit X 0).app (op U) (fun _ => z) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (unit_augmentation X) (op U)) z

/-- Both endpoints of an actual singular edge have the same constant value. -/
theorem augmentation_coface :
    augmentation X ≫ coface X 0 0 = augmentation X ≫ coface X 0 1 := by
  have h : augmentationPresheaf X ≫ cofacePresheaf X 0 0 =
      augmentationPresheaf X ≫ cofacePresheaf X 0 1 := by
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    rfl
  exact ((ringSheafification X).map_comp
    (augmentationPresheaf X) (cofacePresheaf X 0 0)).symm.trans
      ((congrArg (ringSheafification X).map h).trans
        ((ringSheafification X).map_comp (augmentationPresheaf X) (cofacePresheaf X 0 1)))

/-- On each original representative the comparison is the original basis extension. -/
theorem forgetSheafIso_app_unit (n : ℕ) (U : Opens X)
    (a : SingularSimplex U n → ℂ) :
    (forgetSheafIso X n).hom.hom.app (op U) ((unit X n).app (op U) a) =
      (cochainSheafUnit X (AddCommGrpCat.of ℂ) n).app (op U)
        (cochainFromValues U (AddCommGrpCat.of ℂ) n a) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (forgetSheafIso_unit X n) (op U)) a

/-- The native additive augmentation retains its original constant representatives. -/
theorem sheafAugmentation_app_unit (U : Opens X) (z : ℂ) :
    (sheafAugmentation X (AddCommGrpCat.of ℂ)).hom.app (op U)
        ((ConstantSheafFirstCohomology.Constant.unit X (AddCommGrpCat.of ℂ)).app (op U) z) =
      (cochainSheafUnit X (AddCommGrpCat.of ℂ) 0).app (op U)
        (cochainFromValues U (AddCommGrpCat.of ℂ) 0 (fun _ => z)) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (constantUnit_sheafAugmentation X (AddCommGrpCat.of ℂ)) (op U)) z

/-- The actual original additive constant and cochain comparisons preserve augmentation. -/
@[reassoc] theorem augmentation_additive :
    (forgetSheaf X).map (augmentation X) ≫ (forgetSheafIso X 0).hom =
      (SheafConstants.complexAdditiveSheafIso X).hom ≫
        sheafAugmentation X (AddCommGrpCat.of ℂ) := by
  apply OriginalConstants.additive_hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  change ℂ at z
  exact (congrArg ((forgetSheafIso X 0).hom.hom.app U)
    (augmentation_app_unit X U.unop z)).trans
      ((forgetSheafIso_app_unit X 0 U.unop (fun _ => z)).trans
          ((sheafAugmentation_app_unit X U.unop z).symm.trans
            (congrArg ((sheafAugmentation X (AddCommGrpCat.of ℂ)).hom.app U)
              (OriginalConstants.complexAdditiveSheafIso_app_unit X U.unop z).symm)))

end Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains
