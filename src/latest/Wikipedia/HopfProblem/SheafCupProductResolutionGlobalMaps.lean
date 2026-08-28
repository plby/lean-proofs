import Wikipedia.HopfProblem.SheafCupProductResolutionGlobal
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionGlobalMaps

/-!
# Naturality of the actual global-cycle comparisons

These maps are the original section maps. The degree-two homology map
is identified with the genuine cokernel map by actual left homology data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution.Hom

open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}}
  {R S : PartialResolution (TopCat.Sheaf AddCommGrpCat.{0} X)} (φ : R.Hom S)

/-- The original degree-one global-section map of complexes. -/
def globalOneMap : R.globalOneComplex ⟶ S.globalOneComplex :=
  (globalSectionsFunctor X).mapShortComplex.map φ.oneMap

/-- The original degree-two global-section map of complexes. -/
def globalTwoMap : R.globalTwoComplex ⟶ S.globalTwoComplex :=
  (globalSectionsFunctor X).mapShortComplex.map φ.twoMap

theorem globalTruncationInclusion_naturality :
    φ.toAugmentedHom.globalMap ≫ S.globalTruncationInclusion =
      R.globalTruncationInclusion ≫ φ.globalOneMap := by
  let G := (globalSectionsFunctor X).mapShortComplex
  exact ((G.map_comp φ.toAugmentedHom.complex S.truncationInclusion).symm.trans
    (congrArg (fun f => G.map f) φ.truncationInclusion_naturality)).trans
      (G.map_comp R.truncationInclusion φ.oneMap)

theorem globalTruncationHomology_naturality :
    ShortComplex.homologyMap φ.toAugmentedHom.globalMap ≫
        ShortComplex.homologyMap S.globalTruncationInclusion =
      ShortComplex.homologyMap R.globalTruncationInclusion ≫
        ShortComplex.homologyMap φ.globalOneMap := by
  have h := congrArg (fun f : R.toAugmented.globalComplex ⟶ S.globalOneComplex =>
    ShortComplex.homologyMap f) φ.globalTruncationInclusion_naturality
  exact ((ShortComplex.homologyMap_comp φ.toAugmentedHom.globalMap
    S.globalTruncationInclusion).symm.trans h).trans
      (ShortComplex.homologyMap_comp R.globalTruncationInclusion φ.globalOneMap)

/-- Genuine maps of the actual degree-two cycles and their actual cokernels. -/
def globalTwoHomologyMapData : ShortComplex.LeftHomologyMapData φ.globalTwoMap
    R.globalTwoHomologyData S.globalTwoHomologyData where
  φK := (globalSectionsFunctor X).map φ.cyclesTwoMap
  φH := φ.toAugmentedHom.globalCokernelMap
  commi := by
    change (globalSectionsFunctor X).map φ.cyclesTwoMap ≫
        (globalSectionsFunctor X).map (kernel.ι S.d₂) =
      (globalSectionsFunctor X).map (kernel.ι R.d₂) ≫
        (globalSectionsFunctor X).map φ.τ₂
    rw [← Functor.map_comp, ← Functor.map_comp, cyclesTwoMap_ι]
  commf' := by
    change R.globalTwoHomologyData.f' ≫ (globalSectionsFunctor X).map φ.cyclesTwoMap =
      (globalSectionsFunctor X).map φ.τ₁ ≫ S.globalTwoHomologyData.f'
    rw [globalTwoHomologyData_f', globalTwoHomologyData_f']
    change (globalSectionsFunctor X).map R.toCyclesTwo ≫
        (globalSectionsFunctor X).map φ.cyclesTwoMap =
      (globalSectionsFunctor X).map φ.τ₁ ≫ (globalSectionsFunctor X).map S.toCyclesTwo
    exact (((globalSectionsFunctor X).map_comp R.toCyclesTwo φ.cyclesTwoMap).symm.trans
      (congrArg (fun f => (globalSectionsFunctor X).map f)
        φ.toCyclesTwo_naturality.symm)).trans
          ((globalSectionsFunctor X).map_comp φ.τ₁ S.toCyclesTwo)
  commπ := φ.toAugmentedHom.globalCokernelMap_π

/-- The actual cokernel-to-original-homology comparison is natural. -/
theorem globalTwoCokernelIso_naturality :
    φ.toAugmentedHom.globalCokernelMap ≫ S.globalTwoCokernelIso.hom =
      R.globalTwoCokernelIso.hom ≫ ShortComplex.homologyMap φ.globalTwoMap := by
  have hmap : ShortComplex.leftHomologyMap' φ.globalTwoMap
      R.globalTwoHomologyData S.globalTwoHomologyData =
        φ.toAugmentedHom.globalCokernelMap :=
    φ.globalTwoHomologyMapData.leftHomologyMap'_eq
  change φ.toAugmentedHom.globalCokernelMap ≫ S.globalTwoHomologyData.homologyIso.inv =
    R.globalTwoHomologyData.homologyIso.inv ≫ ShortComplex.homologyMap φ.globalTwoMap
  rw [← hmap]
  exact (ShortComplex.LeftHomologyData.leftHomologyIso_inv_naturality
    φ.globalTwoMap R.globalTwoHomologyData S.globalTwoHomologyData).symm

end Wikipedia.HopfProblem.SheafCupProductResolution.PartialResolution.Hom
