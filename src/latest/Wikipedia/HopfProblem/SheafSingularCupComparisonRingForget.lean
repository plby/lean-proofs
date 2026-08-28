import Wikipedia.HopfProblem.CuspNormalizationSheafForgetStalkBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveBasic
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# Forgetting multiplication commutes with actual singular-cochain sheafification

This is the canonical comparison for the original ring-to-additive
forgetful functor and Mathlib's actual sheafification functors. Both the
unit formula and morphism naturality retain the original maps. It will
identify the additive sheaf of ring-valued singular cochains with the
already constructed additive singular-cochain sheaf.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains

open CuspNormalization.SheafForgetStalk (forgetToAdd)

variable (X : TopCat.{0})

/-- The native ring-to-additive functor on sheaves. -/
abbrev forgetSheaf : TopCat.Sheaf CommRingCat.{0} X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  sheafCompose (Opens.grothendieckTopology X) forgetToAdd

abbrev ringSheafification : TopCat.Presheaf CommRingCat.{0} X ⥤
    TopCat.Sheaf CommRingCat.{0} X :=
  presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{0}

abbrev additiveSheafification : TopCat.Presheaf AddCommGrpCat.{0} X ⥤
    TopCat.Sheaf AddCommGrpCat.{0} X :=
  presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

/-- The canonical comparison between the two original sheafifications. -/
def forgetSheafificationIso (P : TopCat.Presheaf CommRingCat.{0} X) :
    (forgetSheaf X).obj ((ringSheafification X).obj P) ≅
      (additiveSheafification X).obj (P ⋙ forgetToAdd) :=
  ((sheafComposeNatIso (Opens.grothendieckTopology X) forgetToAdd
    (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{0})
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{0})).app P).symm

/-- The original ring unit becomes the original additive sheafification unit. -/
@[reassoc] theorem forgetSheafificationIso_unit (P : TopCat.Presheaf CommRingCat.{0} X) :
    Functor.whiskerRight (toSheafify (Opens.grothendieckTopology X) P) forgetToAdd ≫
        (forgetSheafificationIso X P).hom.hom =
      toSheafify (Opens.grothendieckTopology X) (P ⋙ forgetToAdd) :=
  sheafComposeIso_inv_fac (Opens.grothendieckTopology X) forgetToAdd P

/-- The comparison intertwines every actual sheafified ring-presheaf morphism. -/
@[reassoc] theorem forgetSheafificationIso_naturality
    {P Q : TopCat.Presheaf CommRingCat.{0} X} (f : P ⟶ Q) :
    (forgetSheaf X).map ((ringSheafification X).map f) ≫
        (forgetSheafificationIso X Q).hom =
      (forgetSheafificationIso X P).hom ≫
        (additiveSheafification X).map (Functor.whiskerRight f forgetToAdd) :=
  (sheafComposeNatIso (Opens.grothendieckTopology X) forgetToAdd
    (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{0})
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{0})).inv.naturality f

end Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains
