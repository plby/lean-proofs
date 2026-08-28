import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardGlobal
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Genuine higher direct images of abelian sheaves

The functor below is Mathlib's right-derived functor of the actual
topological sheaf pushforward.  In particular, its objects are sheaves,
not a family of groups prescribed by fibre dimensions.  The construction
uses the injective resolutions supplied by the Grothendieck abelian
category of sheaves.  No finiteness, separation, or properness assumption
on the continuous map is needed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafHigherDirectImage

/-- The native small category of sheaves of abelian groups. -/
abbrev AbelianSheaf (X : TopCat.{0}) := TopCat.Sheaf AddCommGrpCat.{0} X

/-- The native pushforward, whose value on an open set is evaluation on
its actual inverse image. -/
abbrev pushforward {X Y : TopCat.{0}} (f : X ⟶ Y) :
    AbelianSheaf X ⥤ AbelianSheaf Y := TopCat.Sheaf.pushforward AddCommGrpCat f

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The genuine right-derived sheaf pushforward `Rⁿf_*`. -/
abbrev functor (n : ℕ) : AbelianSheaf X ⥤ AbelianSheaf Y :=
  (pushforward f).rightDerived n

/-- The genuine higher direct-image sheaf `Rⁿf_*F`. -/
abbrev sheaf (F : AbelianSheaf X) (n : ℕ) : AbelianSheaf Y :=
  (functor f n).obj F

/-- Degree zero is the actual pushforward, because pushforward is a
right adjoint and hence left exact. -/
def zeroIso : functor f 0 ≅ pushforward f :=
  (pushforward f).rightDerivedZeroIsoSelf

/-- Any actual injective resolution computes the genuine higher
direct-image sheaf by the cohomology of its pushed-forward complex. -/
def resolutionIso (F : AbelianSheaf X) (I : InjectiveResolution F) (n : ℕ) :
    sheaf f F n ≅
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).homology n :=
  I.isoRightDerivedObj (pushforward f) n

/-- Higher direct images of an injective sheaf vanish.  This follows
from the native derived-functor construction, without a condition on `f`. -/
theorem injective_isZero (F : AbelianSheaf X) [Injective F] (n : ℕ) :
    IsZero (sheaf f F (n + 1)) :=
  (pushforward f).isZero_rightDerived_obj_injective_succ n F

end Wikipedia.HopfProblem.SheafHigherDirectImage
