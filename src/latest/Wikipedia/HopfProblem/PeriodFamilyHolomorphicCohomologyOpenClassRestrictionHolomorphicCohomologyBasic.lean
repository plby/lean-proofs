import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicEmbeddingInclusion
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingCohomologyBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionCohomology

/-!
# Genuine holomorphic cohomology pullback along an original open embedding

First apply the actual exact restriction-functor map on native Ext.
Then apply the actual holomorphic coefficient morphism given by literal
composition of functions. For an original open-subspace inclusion this
is exactly the existing holomorphic open comparison after native global
restriction. Neither the cohomology nor the scalar structure is redefined.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.HolomorphicCohomology

open HolomorphicSheafCohomology PeriodFamilyHigherDirectImage

variable {E E' H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  (f : TopCat.of M ⟶ TopCat.of N) (hf : Topology.IsOpenEmbedding f)
  (hhol : ContMDiff I J ω f)

/-- The genuine native Ext pullback followed by the original literal
holomorphic coefficient map, in every degree. -/
def pullback (q : ℕ) :
    CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf J N) q →+
      CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) q :=
  (CategoryTheory.Sheaf.H.map (HolomorphicEmbedding.coefficientMap I J f hf hhol) q).comp
    (Embedding.cohomologyMap f hf (HolomorphicFunctionSheaf.additiveSheaf J N) q)

/-- Its literal formula uses only the actual restriction and coefficient maps. -/
theorem pullback_apply (q : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf J N) q) :
    pullback I J f hf hhol q a =
      CategoryTheory.Sheaf.H.map (HolomorphicEmbedding.coefficientMap I J f hf hhol) q
        (Embedding.cohomologyMap f hf (HolomorphicFunctionSheaf.additiveSheaf J N) q a) := rfl

/-- For the original inclusion of an actual open, the map is the
original global restriction followed by the native holomorphic open comparison. -/
theorem pullback_inclusion (A : Opens M) (q : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) q) :
    pullback I I (OpenRestriction.inclusion (X := TopCat.of M) A)
        (OpenRestriction.inclusion_isOpenEmbedding (X := TopCat.of M) A)
        (contMDiff_subtype_val (I := I) (U := A)) q a =
      HolomorphicRestriction.cohomologyEquiv I A q
        (GlobalRestriction.restrictionMap (HolomorphicFunctionSheaf.additiveSheaf I M) A q a) := by
  have hr := Embedding.cohomologyMap_inclusion (X := TopCat.of M) A
    (HolomorphicFunctionSheaf.additiveSheaf I M) q a
  exact (congrArg
    (CategoryTheory.Sheaf.H.map (HolomorphicEmbedding.coefficientMap I I
      (OpenRestriction.inclusion (X := TopCat.of M) A)
      (OpenRestriction.inclusion_isOpenEmbedding (X := TopCat.of M) A)
      (contMDiff_subtype_val (I := I) (U := A))) q) hr).trans
    (congrArg (fun φ => CategoryTheory.Sheaf.H.map φ q
      (OpenRestriction.cohomologyEquiv (X := TopCat.of M) A
        (HolomorphicFunctionSheaf.additiveSheaf I M) q
        (GlobalRestriction.restrictionMap (HolomorphicFunctionSheaf.additiveSheaf I M) A q a)))
      (HolomorphicEmbedding.coefficientMap_inclusion I A))

end OpenClassRestriction.HolomorphicCohomology
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
