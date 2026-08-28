import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicCohomologyComposition
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicCohomologyBiholomorph
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicCohomologyNested
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionFamilyEmbeddings
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesBasic

/-!
# The original neighborhood comparison commutes with actual nested restriction

Both paths use the actual open-submanifold holomorphic sheaves and the
original quotient atlases of the restricted families. The genuine
cohomology-presheaf restriction agrees with the proved holomorphic
pullback, and the original restriction biholomorphisms give a literal
commuting square of continuous maps. Their actual native degree-one
cohomology maps therefore commute as well.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicSheafCohomology PeriodFamilyHigherDirectImage
open HolomorphicCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The existing native neighborhood equivalences intertwine the
original presheaf restriction with actual pullback between the two
original restricted families, on every native degree-one class. -/
theorem neighborhoodCohomologyEquiv_restrict (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (a : OpenClasses.neighborhoodCohomology P W 1) :
    letI := P.totalChartedSpace
    letI := (Restriction.restrictedPeriods P U).totalChartedSpace
    letI := (Restriction.restrictedPeriods P W).totalChartedSpace
    OpenClasses.neighborhoodCohomologyEquiv P U 1
        ((CategoryTheory.Sheaf.cohomologyPresheaf (Zero.totalAdditiveSheaf P) 1).map
          (homOfLE (Zero.basePreimage_mono P h)).op a) =
      pullback IT IT (NestedPeriodCocycle.familyMap P h)
        (nestedFamilyMap_isOpenEmbedding P h) (NestedPeriodCocycle.familyMap_holomorphic P h) 1
        (OpenClasses.neighborhoodCohomologyEquiv P W 1 a) := by
  let := P.totalChartedSpace
  let := (Restriction.restrictedPeriods P U).totalChartedSpace
  let := (Restriction.restrictedPeriods P W).totalChartedSpace
  let eU := Restriction.restrictionBiholomorph P U
  let eW := Restriction.restrictionBiholomorph P W
  let r := nestedInclusion (X := TopCat.of P.TotalSpace) (Zero.basePreimage_mono P h)
  let hr := nestedEmbedding (X := TopCat.of P.TotalSpace) (Zero.basePreimage_mono P h)
  let f := NestedPeriodCocycle.familyMap P h
  let hf := nestedFamilyMap_isOpenEmbedding P h
  let hhol := NestedPeriodCocycle.familyMap_holomorphic P h
  let β := HolomorphicRestriction.cohomologyEquiv IT (Zero.basePreimage P W) 1 a
  let α := (CategoryTheory.Sheaf.cohomologyPresheaf (Zero.totalAdditiveSheaf P) 1).map
    (homOfLE (Zero.basePreimage_mono P h)).op a
  have hn := pullback_nested IT (Zero.basePreimage_mono P h) a
  change Biholomorph.cohomologyEquiv eU 1
      (HolomorphicRestriction.cohomologyEquiv IT (Zero.basePreimage P U) 1 α) =
    pullback IT IT f hf hhol 1 (Biholomorph.cohomologyEquiv eW 1 β)
  calc
    Biholomorph.cohomologyEquiv eU 1
        (HolomorphicRestriction.cohomologyEquiv IT (Zero.basePreimage P U) 1 α) =
        pullback IT IT (Biholomorph.underlyingMap eU) eU.toHomeomorph.isOpenEmbedding
          eU.contMDiff 1
          (HolomorphicRestriction.cohomologyEquiv IT (Zero.basePreimage P U) 1 α) :=
      (pullback_biholomorph IT IT eU _).symm
    _ = pullback IT IT (Biholomorph.underlyingMap eU) eU.toHomeomorph.isOpenEmbedding
        eU.contMDiff 1
        (pullback IT IT r hr (contMDiff_inclusion (Zero.basePreimage_mono P h)) 1 β) :=
      congrArg (pullback IT IT (Biholomorph.underlyingMap eU)
        eU.toHomeomorph.isOpenEmbedding eU.contMDiff 1) hn.symm
    _ = pullback IT IT (Biholomorph.underlyingMap eU ≫ r)
        (hr.comp eU.toHomeomorph.isOpenEmbedding)
        ((contMDiff_inclusion (I := IT) (Zero.basePreimage_mono P h)).comp eU.contMDiff) 1 β :=
      pullback_comp IT IT IT r hr (contMDiff_inclusion (Zero.basePreimage_mono P h))
        (Biholomorph.underlyingMap eU) eU.toHomeomorph.isOpenEmbedding eU.contMDiff β
    _ = pullback IT IT (f ≫ Biholomorph.underlyingMap eW)
        (eW.toHomeomorph.isOpenEmbedding.comp hf) (eW.contMDiff.comp hhol) 1 β := rfl
    _ = pullback IT IT f hf hhol 1
        (pullback IT IT (Biholomorph.underlyingMap eW) eW.toHomeomorph.isOpenEmbedding
          eW.contMDiff 1 β) :=
      (pullback_comp IT IT IT (Biholomorph.underlyingMap eW)
        eW.toHomeomorph.isOpenEmbedding eW.contMDiff f hf hhol β).symm
    _ = pullback IT IT f hf hhol 1 (Biholomorph.cohomologyEquiv eW 1 β) :=
      congrArg (pullback IT IT f hf hhol 1) (pullback_biholomorph IT IT eW β)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
