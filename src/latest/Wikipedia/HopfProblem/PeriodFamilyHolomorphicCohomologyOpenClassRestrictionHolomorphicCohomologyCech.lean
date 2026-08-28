import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicCohomologyBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingCech

/-!
# Literal Čech representatives of actual holomorphic cohomology pullback

The coefficient map to the original pushforward sheaf is exactly
composition of holomorphic functions with the original map. Applying
the proved native open-embedding extension-class comparison identifies
the actual degree-one pullback with the genuine class of that literal
inverse-image cocycle, with no cover or cohomology comparison premise.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.HolomorphicCohomology

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension

variable {E E' H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  (f : TopCat.of M ⟶ TopCat.of N) (hf : Topology.IsOpenEmbedding f)
  (hhol : ContMDiff I J ω f)

/-- The genuine coefficient morphism into original pushforward, built
from actual section restriction and literal holomorphic composition. -/
def pushforwardCoefficientMap :
    HolomorphicFunctionSheaf.additiveSheaf J N ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat f).obj
        (HolomorphicFunctionSheaf.additiveSheaf I M) :=
  EmbeddingCech.coefficientUnit f hf (HolomorphicFunctionSheaf.additiveSheaf J N) ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat f).map
      (HolomorphicEmbedding.coefficientMap I J f hf hhol)

/-- Every actual component is the original function at the original
mapped point, including on arbitrary original ambient opens. -/
theorem pushforwardCoefficientMap_app_apply (U : Opens N)
    (s : HolomorphicFunctionSheaf.Section J N U) (x : (Opens.map f).obj U) :
    Subtype.val ((pushforwardCoefficientMap I J f hf hhol).hom.app (op U) s :
      HolomorphicFunctionSheaf.Section I M ((Opens.map f).obj U)) x =
        s ⟨f x, x.property⟩ := rfl

/-- The genuine native pullback class is the class of the literal
inverse-image cocycle with the actual holomorphic coefficient pullback. -/
theorem pullback_classOf {ι : Type} {U : ι → Opens N}
    (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf J N) U)
    (hU : ∀ x : N, ∃ i : ι, x ∈ U i) :
    pullback I J f hf hhol 1 (classOf c hU) =
      classOf (CechFibre.pullbackCocycle f (pushforwardCoefficientMap I J f hf hhol) c)
        (CechFibre.pullbackCover_covers f hU) :=
  EmbeddingCech.map_cohomologyMap_classOf_pullback f hf c hU
    (HolomorphicEmbedding.coefficientMap I J f hf hhol)

end OpenClassRestriction.HolomorphicCohomology
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
