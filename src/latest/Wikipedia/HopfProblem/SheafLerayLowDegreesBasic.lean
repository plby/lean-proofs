import Wikipedia.HopfProblem.SheafHigherDirectImageResolution
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardComparison
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Native terms in the low-degree Leray comparison

The pushed-forward injective resolution is the actual complex computing
the derived sheaf pushforward.  Its degree-zero homology is the ordinary
pushforward, and its degree-one homology is the actual first higher
direct image.  The following comparisons express the resulting Ext and
Hom groups as Mathlib's existing `Sheaf.H` groups.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

open SheafHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F : AbelianSheaf X}

/-- Degree zero of the actual pushed-forward resolution is the actual
ordinary pushforward, by the native derived-functor comparison. -/
def homologyZeroPushforwardIso (I : InjectiveResolution F) :
    (pushedResolution f I).homology 0 ≅ (pushforward f).obj F :=
  (resolutionIso f F I 0).symm ≪≫ (zeroIso f).app F

/-- The induced comparison on genuine Ext-defined sheaf cohomology. -/
def homologyZeroCohomologyIso (I : InjectiveResolution F) (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} ((pushedResolution f I).homology 0) n) ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) n) :=
  (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n).mapIso
    (homologyZeroPushforwardIso f I)

/-- This is the actual map on cohomology of the canonical sheaf map. -/
@[simp] theorem homologyZeroCohomologyIso_hom_apply (I : InjectiveResolution F) (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} ((pushedResolution f I).homology 0) n) :
    (homologyZeroCohomologyIso f I n).hom x =
      CategoryTheory.Sheaf.H.map (homologyZeroPushforwardIso f I).hom n x := rfl

/-- Global sections of the actual first higher direct image, written
as Hom from the genuine representing integer sheaf into resolution homology. -/
def homologyOneExtZeroIso (I : InjectiveResolution F) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 0) ≅
      AddCommGrpCat.of (integerSheaf Y ⟶ (pushedResolution f I).homology 1) :=
  (Ext.addEquiv₀ (X := integerSheaf Y) (Y := sheaf f F 1)).toAddCommGrpIso ≪≫
    (preadditiveCoyoneda.obj (op (integerSheaf Y))).mapIso (resolutionIso f F I 1)

/-- The degree-zero comparison uses the actual Ext-to-Hom map and
the actual injective-resolution computation of the first derived image. -/
@[simp] theorem homologyOneExtZeroIso_hom_apply (I : InjectiveResolution F)
    (x : CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 0) :
    (homologyOneExtZeroIso f I).hom x = Ext.addEquiv₀ x ≫ (resolutionIso f F I 1).hom := rfl

end Wikipedia.HopfProblem.SheafLerayLowDegrees
