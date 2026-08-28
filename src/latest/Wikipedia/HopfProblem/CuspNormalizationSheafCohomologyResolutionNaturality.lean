import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionGlobalMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExtNaturality

/-!
# Naturality of the genuine sheaf-cohomology comparisons

The degree-one and degree-two isomorphisms commute with actual maps
of augmented resolutions. In particular, these formulas apply to the
actual scalar endomorphisms whenever their sheaf maps commute with the
differentials; no unrelated scalar structure is transported onto H.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

private theorem composition_naturality {A B D A' B' D' : AddCommGrpCat.{0}}
    (a : A ⟶ B) (b : B ⟶ D) (a' : A' ⟶ B') (b' : B' ⟶ D')
    (x : A ⟶ A') (y : B ⟶ B') (z : D ⟶ D')
    (ha : x ≫ a' = a ≫ y) (hb : y ≫ b' = b ≫ z) :
    x ≫ (a' ≫ b') = (a ≫ b) ≫ z := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

namespace AugmentedResolution

variable {X : TopCat.{0}} (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- The canonical comparison of the final Ext-zero cokernel with
the literal global-section cokernel. -/
def extGlobalCokernelIso : cokernel (R.extZeroComplex (unitSheaf X)).g ≅
    cokernel R.globalComplex.g :=
  cokernel.mapIso (R.extZeroComplex (unitSheaf X)).g R.globalComplex.g
    (h0GlobalIso R.complex.X₂) (h0GlobalIso R.complex.X₃)
    (h0GlobalIso_naturality R.complex.g)

@[reassoc] theorem extGlobalCokernelIso_π :
    cokernel.π (R.extZeroComplex (unitSheaf X)).g ≫ R.extGlobalCokernelIso.hom =
      (h0GlobalIso R.complex.X₃).hom ≫ cokernel.π R.globalComplex.g :=
  cokernel.π_desc _ _ _

namespace Hom

variable {R} {S : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X)} (φ : Hom R S)

/-- Naturality of the actual final-cokernel comparison. -/
theorem extGlobalCokernelIso_naturality :
    φ.extCokernelMap (unitSheaf X) ≫ S.extGlobalCokernelIso.hom =
      R.extGlobalCokernelIso.hom ≫ φ.globalCokernelMap := by
  refine comparison_naturality_of_epi
    (cokernel.π (R.extZeroComplex (unitSheaf X)).g)
    (cokernel.π (S.extZeroComplex (unitSheaf X)).g)
    R.extGlobalCokernelIso.hom S.extGlobalCokernelIso.hom
    ((h0GlobalIso R.complex.X₃).hom ≫ cokernel.π R.globalComplex.g)
    ((h0GlobalIso S.complex.X₃).hom ≫ cokernel.π S.globalComplex.g)
    ((extFunctorObj (unitSheaf X) 0).map φ.complex.τ₃)
    (φ.extCokernelMap (unitSheaf X)) φ.globalCokernelMap
    (φ.extCokernelMap_π (unitSheaf X)).symm R.extGlobalCokernelIso_π S.extGlobalCokernelIso_π ?_
  exact composition_naturality
    (h0GlobalIso R.complex.X₃).hom (cokernel.π R.globalComplex.g)
    (h0GlobalIso S.complex.X₃).hom (cokernel.π S.globalComplex.g)
    ((extFunctorObj (unitSheaf X) 0).map φ.complex.τ₃)
    ((globalSectionsFunctor X).map φ.complex.τ₃) φ.globalCokernelMap
    (h0GlobalIso_naturality φ.complex.τ₃) φ.globalCokernelMap_π.symm

/-- Genuine degree-one sheaf cohomology and actual global-section
homology commute with the given map of augmented resolutions. -/
theorem h1Iso_naturality
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)] :
    (CategoryTheory.Sheaf.functorH _ 1).map φ.augmentation ≫ S.h1Iso.hom =
      R.h1Iso.hom ≫ ShortComplex.homologyMap φ.globalMap := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) S.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)›
  change (extFunctorObj (unitSheaf X) 1).map φ.augmentation ≫
      ((S.extOneIso (unitSheaf X)).hom ≫ ShortComplex.homologyMap S.extZeroGlobalIso.hom) =
    ((R.extOneIso (unitSheaf X)).hom ≫ ShortComplex.homologyMap R.extZeroGlobalIso.hom) ≫
      ShortComplex.homologyMap φ.globalMap
  refine composition_naturality
    (R.extOneIso (unitSheaf X)).hom (ShortComplex.homologyMap R.extZeroGlobalIso.hom)
    (S.extOneIso (unitSheaf X)).hom (ShortComplex.homologyMap S.extZeroGlobalIso.hom)
    ((extFunctorObj (unitSheaf X) 1).map φ.augmentation)
    (ShortComplex.homologyMap (φ.extZeroMap (unitSheaf X)))
    (ShortComplex.homologyMap φ.globalMap) (φ.extOneIso_naturality (unitSheaf X)) ?_
  have hmap : ShortComplex.homologyMap (φ.extZeroMap (unitSheaf X) ≫ S.extZeroGlobalIso.hom) =
      ShortComplex.homologyMap (R.extZeroGlobalIso.hom ≫ φ.globalMap) :=
    congrArg (fun k : R.extZeroComplex (unitSheaf X) ⟶ S.globalComplex =>
      ShortComplex.homologyMap k) φ.extZeroGlobalIso_naturality
  exact ((ShortComplex.homologyMap_comp
    (φ.extZeroMap (unitSheaf X)) S.extZeroGlobalIso.hom).symm.trans hmap).trans
      (ShortComplex.homologyMap_comp R.extZeroGlobalIso.hom φ.globalMap)

/-- Genuine degree-two sheaf cohomology and the actual last global
cokernel commute with the given map of augmented resolutions. -/
theorem h2Iso_naturality
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₂ 1)] :
    (CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation ≫ S.h2Iso.hom =
      R.h2Iso.hom ≫ φ.globalCokernelMap := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)›
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) S.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) S.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 2)›
  let : Subsingleton (Ext.{0} (unitSheaf X) S.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₂ 1)›
  change (extFunctorObj (unitSheaf X) 2).map φ.augmentation ≫
      ((S.extTwoIso (unitSheaf X)).hom ≫ S.extGlobalCokernelIso.hom) =
    ((R.extTwoIso (unitSheaf X)).hom ≫ R.extGlobalCokernelIso.hom) ≫ φ.globalCokernelMap
  exact composition_naturality
    (R.extTwoIso (unitSheaf X)).hom R.extGlobalCokernelIso.hom
    (S.extTwoIso (unitSheaf X)).hom S.extGlobalCokernelIso.hom
    ((extFunctorObj (unitSheaf X) 2).map φ.augmentation)
    (φ.extCokernelMap (unitSheaf X)) φ.globalCokernelMap
    (φ.extTwoIso_naturality (unitSheaf X)) φ.extGlobalCokernelIso_naturality

end Hom

end AugmentedResolution

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
