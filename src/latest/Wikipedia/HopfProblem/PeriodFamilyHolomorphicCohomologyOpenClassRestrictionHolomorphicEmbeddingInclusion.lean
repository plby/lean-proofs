import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicEmbeddingSheaf
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionSheaf

/-!
# The original open-submanifold coefficient map is literal pullback

For an actual open inclusion, the general section pullback is precisely
the existing flattening algebra equivalence. The induced coefficient
morphism is the original holomorphic restriction sheaf isomorphism,
with the original ambient atlas and its inherited open charts.
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

/-- On every actual submanifold open, the general pullback is the
original complex-algebra flattening map. -/
theorem sectionPullback_inclusion (A : Opens M) (U : Opens A) :
    sectionPullback I I (OpenRestriction.inclusion (X := TopCat.of M) A)
      (OpenRestriction.inclusion_isOpenEmbedding (X := TopCat.of M) A)
      (contMDiff_subtype_val (I := I) (U := A)) U =
        (HolomorphicRestriction.sectionEquiv I A U).toAlgHom := by
  apply AlgHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The coefficient morphism for the original open inclusion equals
the original holomorphic open-restriction sheaf isomorphism itself. -/
theorem coefficientMap_inclusion (A : Opens M) :
    coefficientMap I I (OpenRestriction.inclusion (X := TopCat.of M) A)
      (OpenRestriction.inclusion_isOpenEmbedding (X := TopCat.of M) A)
      (contMDiff_subtype_val (I := I) (U := A)) =
        (HolomorphicRestriction.sheafIso I A).hom := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

end OpenClassRestriction.HolomorphicEmbedding
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
