import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtTwo
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtOneNaturality

/-!
# Naturality of the native degree-two cochain-resolution comparison
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt

open CuspNormalization.SheafCohomologyResolution

private theorem composition_naturality_two {C : Type*} [Category C]
    {A B D A' B' D' : C}
    (a : A ⟶ B) (b : B ⟶ D) (a' : A' ⟶ B') (b' : B' ⟶ D')
    (x : A ⟶ A') (y : B ⟶ B') (z : D ⟶ D')
    (ha : x ≫ a' = a ≫ y) (hb : y ≫ b' = b ≫ z) :
    x ≫ (a' ≫ b') = (a ≫ b) ≫ z := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

namespace CochainResolution.Hom

variable {X : TopCat.{0}}
  {R S : CochainResolution (TopCat.Sheaf AddCommGrpCat.{0} X)} (φ : Hom R S)

theorem globalSecondHomologyIso_naturality :
    φ.truncationMap.globalCokernelMap ≫ S.globalSecondHomologyIso.hom =
      R.globalSecondHomologyIso.hom ≫ HomologicalComplex.homologyMap φ.globalMap 2 :=
  CycleCokernel.cokernelIsoHomology₂_hom_naturality (globalSectionsFunctor X) φ.complex

/-- The native degree-two sheaf-cohomology comparison commutes with
the actual augmented cochain map, including genuine coefficient maps. -/
theorem h2Iso_naturality
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 1) 1)] :
    (CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation ≫ S.h2Iso.hom =
      R.h2Iso.hom ≫ HomologicalComplex.homologyMap φ.globalMap 2 := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.truncation.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 1)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.truncation.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 2)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.truncation.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 1) 1)›
  exact composition_naturality_two
    R.truncation.h2Iso.hom R.globalSecondHomologyIso.hom
    S.truncation.h2Iso.hom S.globalSecondHomologyIso.hom
    ((CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation)
    φ.truncationMap.globalCokernelMap
    (HomologicalComplex.homologyMap φ.globalMap 2)
    φ.truncationMap.h2Iso_naturality φ.globalSecondHomologyIso_naturality

end CochainResolution.Hom

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt
