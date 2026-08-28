import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtTwo
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionNaturality

/-!
# Explicit components of the native low-degree comparison maps

These generic identities expose only the outer composition of the
original isomorphisms.  They let concrete pushforward proofs compose
already established squares without unfolding their resolutions.
The hypotheses concern only native sheaf cohomology.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

open CuspNormalization.SheafCohomologyResolution

/-- Compose two already proved comparison squares using named
formulas for the outer maps.  The proof does not unfold those maps. -/
theorem composition_eq_of_hom_forms {C : Type*} [Category C]
    {H B T H' B' : C} (x : H ⟶ H') (e : H ⟶ T) (e' : H' ⟶ T)
    (a : H ⟶ B) (b : B ⟶ T) (a' : H' ⟶ B') (b' : B' ⟶ T) (y : B ⟶ B')
    (he : e = a ≫ b) (he' : e' = a' ≫ b')
    (ha : x ≫ a' = a ≫ y) (hb : y ≫ b' = b) : x ≫ e' = e := by
  rw [he, he', ← Category.assoc, ha, Category.assoc, hb]

variable {X : TopCat.{0}}

/-- The original degree-one sheaf comparison is the composite of the
original Ext comparison and the native degree-zero global comparison. -/
theorem augmented_h1Iso_hom
    (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)] :
    letI : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
      ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
    R.h1Iso.hom = (R.extOneIso (unitSheaf X)).hom ≫
      ShortComplex.homologyMap R.extZeroGlobalIso.hom := rfl

/-- The original degree-two sheaf comparison is the composite of the
original Ext comparison and the actual global-section cokernel comparison. -/
theorem augmented_h2Iso_hom
    (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)] :
    letI : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
      ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
    letI : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 2) :=
      ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)›
    letI : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₂ 1) :=
      ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)›
    R.h2Iso.hom = (R.extTwoIso (unitSheaf X)).hom ≫ R.extGlobalCokernelIso.hom := rfl

/-- The original degree-one cochain-resolution comparison factors
through the genuine augmented truncation. -/
theorem cochain_h1Iso_hom
    (R : LowExt.CochainResolution (TopCat.Sheaf AddCommGrpCat.{0} X))
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)] :
    letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1) :=
      ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)›
    R.h1Iso.hom = R.truncation.h1Iso.hom ≫ R.globalFirstHomologyIso.hom := rfl

/-- The original degree-two cochain-resolution comparison factors
through the genuine augmented truncation and the preserved kernel. -/
theorem cochain_h2Iso_hom
    (R : LowExt.CochainResolution (TopCat.Sheaf AddCommGrpCat.{0} X))
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)] :
    letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1) :=
      ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)›
    letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 2) :=
      ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)›
    letI : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₂ 1) :=
      ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)›
    R.h2Iso.hom = R.truncation.h2Iso.hom ≫ R.globalSecondHomologyIso.hom := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
