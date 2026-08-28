import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtOne
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionNaturality

/-!
# Naturality of the native degree-one cochain-resolution comparison
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt

open CuspNormalization.SheafCohomologyResolution

private theorem composition_naturality {C : Type*} [Category C]
    {A B D A' B' D' : C}
    (a : A ⟶ B) (b : B ⟶ D) (a' : A' ⟶ B') (b' : B' ⟶ D')
    (x : A ⟶ A') (y : B ⟶ B') (z : D ⟶ D')
    (ha : x ≫ a' = a ≫ y) (hb : y ≫ b' = b ≫ z) :
    x ≫ (a' ≫ b') = (a ≫ b) ≫ z := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

namespace CochainResolution.Hom

variable {X : TopCat.{0}}
  {R S : CochainResolution (TopCat.Sheaf AddCommGrpCat.{0} X)} (φ : Hom R S)

/-- The given cochain map evaluated on actual global sections. -/
def globalMap : R.globalCochainComplex ⟶ S.globalCochainComplex :=
  ((globalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.complex

/-- Its literal degree-zero, one and two short complex map. -/
def globalShortMap : R.globalCochainComplex.sc' 0 1 2 ⟶
    S.globalCochainComplex.sc' 0 1 2 :=
  (HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{0} (ComplexShape.up ℕ) 0 1 2).map
    φ.globalMap

theorem globalShortInclusion_naturality :
    φ.truncationMap.globalMap ≫ S.globalShortInclusion =
      R.globalShortInclusion ≫ φ.globalShortMap := by
  let G := (globalSectionsFunctor X).mapShortComplex
  exact (G.map_comp φ.shortMap S.shortInclusion).symm.trans
    ((G.congr_map φ.shortInclusion_naturality).trans
      (G.map_comp R.shortInclusion
        ((HomologicalComplex.shortComplexFunctor' _ (ComplexShape.up ℕ) 0 1 2).map
          φ.complex)))

theorem globalFirstHomologyIso_naturality :
    ShortComplex.homologyMap φ.truncationMap.globalMap ≫ S.globalFirstHomologyIso.hom =
      R.globalFirstHomologyIso.hom ≫ HomologicalComplex.homologyMap φ.globalMap 1 := by
  let eR := R.globalCochainComplex.isoSc' 0 1 2
    ((ComplexShape.up ℕ).prev_eq' (by rfl))
    ((ComplexShape.up ℕ).next_eq' (by rfl))
  let eS := S.globalCochainComplex.isoSc' 0 1 2
    ((ComplexShape.up ℕ).prev_eq' (by rfl))
    ((ComplexShape.up ℕ).next_eq' (by rfl))
  have h₁ : ShortComplex.homologyMap φ.truncationMap.globalMap ≫
      ShortComplex.homologyMap S.globalShortInclusion =
    ShortComplex.homologyMap R.globalShortInclusion ≫
      ShortComplex.homologyMap φ.globalShortMap :=
    (ShortComplex.homologyMap_comp φ.truncationMap.globalMap S.globalShortInclusion).symm.trans
      ((congrArg (fun k : R.truncation.globalComplex ⟶
          S.globalCochainComplex.sc' 0 1 2 => ShortComplex.homologyMap k)
        φ.globalShortInclusion_naturality).trans
        (ShortComplex.homologyMap_comp R.globalShortInclusion φ.globalShortMap))
  have hsq : φ.globalShortMap ≫ eS.inv = eR.inv ≫
      (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) 1).map
        φ.globalMap :=
    (HomologicalComplex.natIsoSc' AddCommGrpCat.{0} (ComplexShape.up ℕ) 0 1 2
      ((ComplexShape.up ℕ).prev_eq' (by rfl))
      ((ComplexShape.up ℕ).next_eq' (by rfl))).inv.naturality φ.globalMap
  have h₂ : ShortComplex.homologyMap φ.globalShortMap ≫ ShortComplex.homologyMap eS.inv =
      ShortComplex.homologyMap eR.inv ≫ HomologicalComplex.homologyMap φ.globalMap 1 :=
    (ShortComplex.homologyMap_comp φ.globalShortMap eS.inv).symm.trans
      ((congrArg (fun k : R.globalCochainComplex.sc' 0 1 2 ⟶
          S.globalCochainComplex.sc 1 => ShortComplex.homologyMap k) hsq).trans
        (ShortComplex.homologyMap_comp eR.inv
          ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{0}
            (ComplexShape.up ℕ) 1).map φ.globalMap)))
  exact composition_naturality
    (ShortComplex.homologyMap R.globalShortInclusion) (ShortComplex.homologyMap eR.inv)
    (ShortComplex.homologyMap S.globalShortInclusion) (ShortComplex.homologyMap eS.inv)
    (ShortComplex.homologyMap φ.truncationMap.globalMap)
    (ShortComplex.homologyMap φ.globalShortMap) (HomologicalComplex.homologyMap φ.globalMap 1)
    h₁ h₂

/-- The native sheaf-cohomology comparison commutes with the actual
augmented cochain map. This applies in particular to coefficient maps. -/
theorem h1Iso_naturality
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 1)] :
    (CategoryTheory.Sheaf.functorH _ 1).map φ.augmentation ≫ S.h1Iso.hom =
      R.h1Iso.hom ≫ HomologicalComplex.homologyMap φ.globalMap 1 := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.truncation.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (S.K.X 0) 1)›
  exact composition_naturality
    R.truncation.h1Iso.hom R.globalFirstHomologyIso.hom
    S.truncation.h1Iso.hom S.globalFirstHomologyIso.hom
    ((CategoryTheory.Sheaf.functorH _ 1).map φ.augmentation)
    (ShortComplex.homologyMap φ.truncationMap.globalMap)
    (HomologicalComplex.homologyMap φ.globalMap 1)
    φ.truncationMap.h1Iso_naturality φ.globalFirstHomologyIso_naturality

end CochainResolution.Hom

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt
