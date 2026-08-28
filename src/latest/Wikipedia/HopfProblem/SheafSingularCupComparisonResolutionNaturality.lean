import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionBasic
import Wikipedia.HopfProblem.SheafCupProductResolutionGlobalMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionNaturality

/-!
# Naturality of the original partial-resolution maps under acyclicity

The augmentation map on genuine sheaf cohomology corresponds to the
original maps of global sections, using only the stated actual low-degree
vanishings. Every intermediate map is the original truncation or cokernel
map already constructed for partial resolutions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.Resolution

private theorem comparison_compose {A B D A' B' D' : AddCommGrpCat.{0}}
    (a : A ⟶ B) (b : B ⟶ D) (a' : A' ⟶ B') (b' : B' ⟶ D')
    (x : A ⟶ A') (y : B ⟶ B') (z : D ⟶ D')
    (ha : x ≫ a' = a ≫ y) (hb : y ≫ b' = b ≫ z) :
    x ≫ (a' ≫ b') = (a ≫ b) ≫ z := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

end Wikipedia.HopfProblem.SheafSingularCupComparison.Resolution

namespace Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution.Hom

open CuspNormalization.SheafCohomologyResolution
open SheafSingularCupComparison.Resolution

variable {X : TopCat.{0}}
  {R S : PartialResolution (TopCat.Sheaf AddCommGrpCat.{0} X)} (φ : R.Hom S)

theorem h1IsoAcyclic_naturality [Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₀ 1)] :
    (CategoryTheory.Sheaf.functorH _ 1).map φ.augmentation ≫ S.h1IsoAcyclic.hom =
      R.h1IsoAcyclic.hom ≫ ShortComplex.homologyMap φ.globalOneMap := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1))
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.toAugmented.complex.X₁ 1) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₀ 1))
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

theorem h2IsoAcyclic_naturality [Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₀ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₀ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₁ 1)] :
    (CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation ≫ S.h2IsoAcyclic.hom =
      R.h2IsoAcyclic.hom ≫ ShortComplex.homologyMap φ.globalTwoMap := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 1) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1))
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₁ 2) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 2))
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.toAugmented.complex.X₂ 1) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₁ 1))
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.toAugmented.complex.X₁ 1) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₀ 1))
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.toAugmented.complex.X₁ 2) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₀ 2))
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.toAugmented.complex.X₂ 1) :=
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H.{0} S.I₁ 1))
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

end Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution.Hom
