import Wikipedia.HopfProblem.SheafCupProductResolutionCohomology
import Wikipedia.HopfProblem.SheafCupProductResolutionGlobalMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionNaturality

/-!
# Naturality of the native partial-resolution comparisons

The original augmentation map on genuine sheaf cohomology corresponds
to the original maps on global terms. No identification of cohomology
or naturality is included as an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProductResolution

private theorem comparison_compose {A B D A' B' D' : AddCommGrpCat.{0}}
    (a : A ⟶ B) (b : B ⟶ D) (a' : A' ⟶ B') (b' : B' ⟶ D')
    (x : A ⟶ A') (y : B ⟶ B') (z : D ⟶ D')
    (ha : x ≫ a' = a ≫ y) (hb : y ≫ b' = b ≫ z) :
    x ≫ (a' ≫ b') = (a ≫ b) ≫ z := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

namespace PartialResolution.Hom

open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}}
  {R S : PartialResolution (TopCat.Sheaf AddCommGrpCat.{0} X)} (φ : R.Hom S)

/-- The actual H¹ comparison is natural for the original partial-resolution maps. -/
theorem h1Iso_naturality [Injective R.I₀] [Injective S.I₀] :
    (CategoryTheory.Sheaf.functorH _ 1).map φ.augmentation ≫ S.h1Iso.hom =
      R.h1Iso.hom ≫ ShortComplex.homologyMap φ.globalOneMap := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) :=
    injective_higher_subsingleton R.I₀ 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.toAugmented.complex.X₁ 1) :=
    injective_higher_subsingleton S.I₀ 0
  change (CategoryTheory.Sheaf.functorH _ 1).map φ.augmentation ≫
      (S.toAugmented.h1Iso.hom ≫ ShortComplex.homologyMap S.globalTruncationInclusion) =
    (R.toAugmented.h1Iso.hom ≫ ShortComplex.homologyMap R.globalTruncationInclusion) ≫
      ShortComplex.homologyMap φ.globalOneMap
  exact comparison_compose
    R.toAugmented.h1Iso.hom (ShortComplex.homologyMap R.globalTruncationInclusion)
    S.toAugmented.h1Iso.hom (ShortComplex.homologyMap S.globalTruncationInclusion)
    ((CategoryTheory.Sheaf.functorH _ 1).map φ.augmentation)
    (ShortComplex.homologyMap φ.toAugmentedHom.globalMap)
    (ShortComplex.homologyMap φ.globalOneMap)
    φ.toAugmentedHom.h1Iso_naturality φ.globalTruncationHomology_naturality

/-- The actual H² comparison is natural for the original partial-resolution maps. -/
theorem h2Iso_naturality [Injective R.I₀] [Injective R.I₁]
    [Injective S.I₀] [Injective S.I₁] :
    (CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation ≫ S.h2Iso.hom =
      R.h2Iso.hom ≫ ShortComplex.homologyMap φ.globalTwoMap := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) :=
    injective_higher_subsingleton R.I₀ 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 2) :=
    injective_higher_subsingleton R.I₀ 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₂ 1) :=
    injective_higher_subsingleton R.I₁ 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.toAugmented.complex.X₁ 1) :=
    injective_higher_subsingleton S.I₀ 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.toAugmented.complex.X₁ 2) :=
    injective_higher_subsingleton S.I₀ 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.toAugmented.complex.X₂ 1) :=
    injective_higher_subsingleton S.I₁ 0
  change (CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation ≫
      (S.toAugmented.h2Iso.hom ≫ S.globalTwoCokernelIso.hom) =
    (R.toAugmented.h2Iso.hom ≫ R.globalTwoCokernelIso.hom) ≫
      ShortComplex.homologyMap φ.globalTwoMap
  exact comparison_compose
    R.toAugmented.h2Iso.hom R.globalTwoCokernelIso.hom
    S.toAugmented.h2Iso.hom S.globalTwoCokernelIso.hom
    ((CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation)
    φ.toAugmentedHom.globalCokernelMap (ShortComplex.homologyMap φ.globalTwoMap)
    φ.toAugmentedHom.h2Iso_naturality φ.globalTwoCokernelIso_naturality

end PartialResolution.Hom

end Wikipedia.HopfProblem.SheafCupProductResolution
