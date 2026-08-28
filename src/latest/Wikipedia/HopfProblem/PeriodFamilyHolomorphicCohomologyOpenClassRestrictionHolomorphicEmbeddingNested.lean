import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicEmbeddingInclusion
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicEmbeddingComposition
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedGeometry

/-!
# The holomorphic coefficient square for original nested opens

For original opens `U ≤ W` of the given manifold, the actual inclusion
`U → W` pulls back the original holomorphic functions. Its coefficient
map commutes with the two original ambient restriction isomorphisms,
through the canonical comparison of the literal restriction functors.
All charts are the original atlas and its inherited open-subspace charts.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.HolomorphicEmbedding

open HolomorphicSheafCohomology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {U W : Opens M}

/-- The genuine coefficient map for the actual nested inclusion commutes
with the original ambient holomorphic restriction isomorphisms. -/
theorem coefficientMap_nested (h : U ≤ W) :
    (Embedding.restriction (nestedInclusion (X := TopCat.of M) h)
        (nestedEmbedding (X := TopCat.of M) h)).map
          (HolomorphicRestriction.sheafIso I W).hom ≫
      coefficientMap I I (nestedInclusion (X := TopCat.of M) h)
        (nestedEmbedding (X := TopCat.of M) h) (contMDiff_inclusion h) =
    (nestedRestrictionIso (X := TopCat.of M) h).hom.app
        (HolomorphicFunctionSheaf.additiveSheaf I M) ≫
      (HolomorphicRestriction.sheafIso I U).hom := by
  rw [← coefficientMap_inclusion I W, ← coefficientMap_inclusion I U]
  exact coefficientMap_comp I I I
    (OpenRestriction.inclusion (X := TopCat.of M) W)
    (OpenRestriction.inclusion_isOpenEmbedding (X := TopCat.of M) W)
    (contMDiff_subtype_val (I := I) (U := W))
    (nestedInclusion (X := TopCat.of M) h)
    (nestedEmbedding (X := TopCat.of M) h) (contMDiff_inclusion h)

end OpenClassRestriction.HolomorphicEmbedding
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
