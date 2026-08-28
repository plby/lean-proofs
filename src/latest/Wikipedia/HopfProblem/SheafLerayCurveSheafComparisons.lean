import Wikipedia.HopfProblem.SheafLerayLowDegreesBasic

/-!
# Native all-degree Leray term comparisons

The homology of the actual pushed-forward injective resolution computes
every genuine higher direct image.  Applying the existing sheaf-cohomology
functor gives the comparison in every pair of degrees.  In degree zero,
the native Ext-to-Hom equivalence identifies sections with morphisms from
the representing integer sheaf into that same resolution homology.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayCurve

open SheafHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {F : AbelianSheaf X}

/-- Genuine cohomology of resolution homology is genuine cohomology of
the corresponding higher direct image, in every pair of degrees. -/
def resolutionCohomologyIso (I : InjectiveResolution F) (q p : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} ((pushedResolution f I).homology q) p) ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (sheaf f F q) p) :=
  (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) p).mapIso
    (resolutionIso f F I q).symm

/-- The comparison uses the original cohomology map of the original
derived-resolution isomorphism. -/
@[simp] theorem resolutionCohomologyIso_hom_apply (I : InjectiveResolution F) (q p : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} ((pushedResolution f I).homology q) p) :
    (resolutionCohomologyIso f I q p).hom x =
      CategoryTheory.Sheaf.H.map (resolutionIso f F I q).inv p x := rfl

/-- The inverse comparison is also the original sheaf-cohomology map. -/
@[simp] theorem resolutionCohomologyIso_inv_apply (I : InjectiveResolution F) (q p : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} (sheaf f F q) p) :
    (resolutionCohomologyIso f I q p).inv x =
      CategoryTheory.Sheaf.H.map (resolutionIso f F I q).hom p x := rfl

/-- Degree-zero cohomology of the actual higher direct image is Hom from
the genuine representing integer sheaf into resolution homology. -/
def resolutionExtZeroIso (I : InjectiveResolution F) (q : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (sheaf f F q) 0) ≅
      AddCommGrpCat.of (integerSheaf Y ⟶ (pushedResolution f I).homology q) :=
  (Ext.addEquiv₀ (X := integerSheaf Y) (Y := sheaf f F q)).toAddCommGrpIso ≪≫
    (preadditiveCoyoneda.obj (op (integerSheaf Y))).mapIso (resolutionIso f F I q)

/-- The forward comparison is the native Ext-to-Hom map followed by
the actual injective-resolution computation of the higher direct image. -/
@[simp] theorem resolutionExtZeroIso_hom_apply (I : InjectiveResolution F) (q : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} (sheaf f F q) 0) :
    (resolutionExtZeroIso f I q).hom x =
      Ext.addEquiv₀ x ≫ (resolutionIso f F I q).hom := rfl

end Wikipedia.HopfProblem.SheafLerayCurve
