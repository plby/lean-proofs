import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionFamilyBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedPeriodCocycleBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedGeometry
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBiholomorph

/-!
# The actual open embeddings between original restricted families

The maps change only the original base-subtype coordinate. They are
therefore genuine open embeddings of the original product topologies.
The original restriction biholomorphisms give literal commuting squares
with the corresponding full-preimage inclusions, retaining every native
quotient atlas in their holomorphic formulations.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicSheafCohomology PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The literal family map is an actual open embedding, without separation assumptions. -/
theorem familyMap_isOpenEmbedding (P : HolomorphicPeriodMap V B) (A : Opens B) :
    Topology.IsOpenEmbedding (familyMap P A) :=
  A.isOpenEmbedding'.prodMap Topology.IsOpenEmbedding.id

/-- The direct native map between nested original families is an open embedding. -/
theorem nestedFamilyMap_isOpenEmbedding (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) :
    Topology.IsOpenEmbedding (NestedPeriodCocycle.familyMap P h) :=
  (Opens.isOpenEmbedding_of_le h).prodMap Topology.IsOpenEmbedding.id

/-- Both paths to the original whole family are the same actual map. -/
@[simp] theorem nestedFamilyMap_comp_familyMap (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) :
    NestedPeriodCocycle.familyMap P h ≫ familyMap P W = familyMap P U := rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The original total-family inclusion factors through its original
restriction biholomorphism and the actual full-preimage open inclusion. -/
theorem restrictionBiholomorph_comp_inclusion (P : HolomorphicPeriodMap V B) (A : Opens B) :
    letI := P.totalChartedSpace
    letI := (Restriction.restrictedPeriods P A).totalChartedSpace
    Biholomorph.underlyingMap (Restriction.restrictionBiholomorph P A) ≫
      OpenRestriction.inclusion (X := TopCat.of P.TotalSpace) (Zero.basePreimage P A) =
        familyMap P A := by
  let := P.totalChartedSpace
  let := (Restriction.restrictedPeriods P A).totalChartedSpace
  rfl

/-- The original biholomorphic comparison square commutes as an equality
of actual continuous maps, not merely as an unproved cohomology square. -/
theorem restrictionBiholomorph_nested_square (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) :
    letI := P.totalChartedSpace
    letI := (Restriction.restrictedPeriods P U).totalChartedSpace
    letI := (Restriction.restrictedPeriods P W).totalChartedSpace
    Biholomorph.underlyingMap (Restriction.restrictionBiholomorph P U) ≫
        nestedInclusion (X := TopCat.of P.TotalSpace) (Zero.basePreimage_mono P h) =
      NestedPeriodCocycle.familyMap P h ≫
        Biholomorph.underlyingMap (Restriction.restrictionBiholomorph P W) := by
  let := P.totalChartedSpace
  let := (Restriction.restrictedPeriods P U).totalChartedSpace
  let := (Restriction.restrictedPeriods P W).totalChartedSpace
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
