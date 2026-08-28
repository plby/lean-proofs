import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreInteger
import Mathlib.CategoryTheory.Sites.Continuous

/-!
# The native integer endpoint along a continuous functor of open sites

The unit is obtained by the genuine sheafification of the constant integer
presheaf. Its target is the actual continuous-site pushforward, and its
presheaf-unit formula is literal precomposition on opens.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.ImageInteger

open CuspNormalization.SheafCohomologyFinitePushforward
open HolomorphicPicard.CechExtension

variable {T X : TopCat.{0}} (J : Opens T ⥤ Opens X)
  [J.IsContinuous (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)]

/-- The actual integer-sheaf endpoint induced by native constant-presheaf
sheafification, for a continuous functor of the original open sites. -/
def unit : integerSheaf T ⟶
    (J.sheafPushforwardContinuous AddCommGrpCat
      (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)).obj (integerSheaf X) where
  hom := sheafifyLift (Opens.grothendieckTopology T)
    (Functor.whiskerLeft J.op (degreeUnit X))
    ((J.sheafPushforwardContinuous AddCommGrpCat
      (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)).obj
        (integerSheaf X)).property

/-- The defining triangle is an equality of actual presheaf morphisms. -/
theorem degreeUnit_unit :
    degreeUnit T ≫ (unit J).hom = Functor.whiskerLeft J.op (degreeUnit X) :=
  toSheafify_sheafifyLift (Opens.grothendieckTopology T) _ _

/-- On every original open, the endpoint preserves each original constant
integer section, evaluated at its literal image under the open-site functor. -/
theorem unit_degreeUnit_app (W : Opens T) (n : ULift.{0} ℤ) :
    (unit J).hom.app (op W) ((degreeUnit T).app (op W) n) =
      (degreeUnit X).app (op (J.obj W)) n :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (degreeUnit_unit J) (op W)) n

/-- Native sheafification makes the degree-unit formula determine the actual
integer endpoint uniquely; no isomorphism of endpoints is assumed. -/
theorem unit_unique
    (η : integerSheaf T ⟶
      (J.sheafPushforwardContinuous AddCommGrpCat
        (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)).obj (integerSheaf X))
    (hη : degreeUnit T ≫ η.hom = Functor.whiskerLeft J.op (degreeUnit X)) : η = unit J := by
  apply CategoryTheory.Sheaf.hom_ext
  exact sheafify_hom_ext (Opens.grothendieckTopology T) η.hom (unit J).hom
    ((J.sheafPushforwardContinuous AddCommGrpCat
      (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)).obj
        (integerSheaf X)).property (hη.trans (degreeUnit_unit J).symm)

end OpenClassRestriction.ImageInteger
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
