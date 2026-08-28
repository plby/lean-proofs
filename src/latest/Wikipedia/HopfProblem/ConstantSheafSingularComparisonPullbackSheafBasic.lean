import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafRaw
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafLift
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSheafBasic

/-!
# Continuous maps act on the original sheafified cochains

The native presheaf pullback on preimage opens extends through the actual
sheafification unit. This gives the genuine map of cochain sheaves into
the native pushforward. The original differentials and the actual
constant-sheaf augmentation commute with these maps.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (A : AddCommGrpCat.{0})

/-- The map on the actual singular cochain sheaves induced by the
original continuous map and original singular pullback. -/
def cochainPullback (n : ℕ) :
    cochainSheaf Y A n ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj
      (cochainSheaf X A n) :=
  sheafifyPullback f (rawPullback f A n)

/-- Original raw cochains retain exactly their original pullback under
the native sheafification units. -/
@[reassoc]
theorem unit_cochainPullback (n : ℕ) :
    cochainSheafUnit Y A n ≫ (cochainPullback f A n).hom =
      rawPullback f A n ≫ (TopCat.Presheaf.pushforward AddCommGrpCat f).map
        (cochainSheafUnit X A n) :=
  unit_sheafifyPullback f (rawPullback f A n)

/-- Pointwise form of the actual unit compatibility on each original open. -/
@[simp]
theorem cochainPullback_app_unit (n : ℕ) (U : Opens Y) (φ : Cochains U A n) :
    (cochainPullback f A n).hom.app (op U)
        ((cochainSheafUnit Y A n).app (op U) φ) =
      (cochainSheafUnit X A n).app (op ((Opens.map f).obj U))
        ((rawPullback f A n).app (op U) φ) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (unit_cochainPullback f A n) (op U)) φ

/-- Pullback commutes with every original sheafified differential. -/
@[reassoc]
theorem cochainPullback_d (i j : ℕ) :
    cochainPullback f A i ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map
        (sheafDifferential X A i j) =
      sheafDifferential Y A i j ≫ cochainPullback f A j :=
  (sheafifyPullback_naturality f (presheafDifferential Y A i j)
    (presheafDifferential X A i j) (rawPullback f A i) (rawPullback f A j)
    (rawPullback_d f A i j).symm).symm

/-- The native constant sheaf map into its actual pushforward keeps
the original coefficient values on every preimage open. -/
def constantPullback : ConstantSheafFirstCohomology.Constant.sheaf Y A ⟶
    (TopCat.Sheaf.pushforward AddCommGrpCat f).obj
      (ConstantSheafFirstCohomology.Constant.sheaf X A) :=
  sheafifyPullback f (rawConstantPullback f A)

/-- The constant-sheaf map intertwines the genuine constant units. -/
@[reassoc]
theorem unit_constantPullback :
    ConstantSheafFirstCohomology.Constant.unit Y A ≫ (constantPullback f A).hom =
      rawConstantPullback f A ≫ (TopCat.Presheaf.pushforward AddCommGrpCat f).map
        (ConstantSheafFirstCohomology.Constant.unit X A) :=
  unit_sheafifyPullback f (rawConstantPullback f A)

/-- The original coefficient value is unchanged by the actual constant
sheaf pullback on any open set. -/
@[simp]
theorem constantPullback_app_unit (U : Opens Y) (a : A) :
    (constantPullback f A).hom.app (op U)
        ((ConstantSheafFirstCohomology.Constant.unit Y A).app (op U) a) =
      (ConstantSheafFirstCohomology.Constant.unit X A).app
        (op ((Opens.map f).obj U)) a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (unit_constantPullback f A) (op U)) a

/-- The genuine constant augmentation is natural under every original
continuous map, before taking cohomology. -/
@[reassoc]
theorem cochainPullback_augmentation :
    sheafAugmentation Y A ≫ cochainPullback f A 0 =
      constantPullback f A ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map
        (sheafAugmentation X A) :=
  sheafifyPullback_naturality f (constantAugmentation Y A) (constantAugmentation X A)
    (rawConstantPullback f A) (rawPullback f A 0) (rawPullback_constantAugmentation f A)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf
