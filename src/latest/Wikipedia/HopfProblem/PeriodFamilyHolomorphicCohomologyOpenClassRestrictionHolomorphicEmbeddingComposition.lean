import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicEmbeddingSheaf
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingComposition

/-!
# Composition of the actual holomorphic coefficient maps

Pullback of an original holomorphic function along two holomorphic open
embeddings is pullback along their actual composite. The comparison uses
the canonical composition isomorphism of the literal restriction functors.
The identity coefficient map is the corresponding identity comparison.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.HolomorphicEmbedding

variable {E H E' H' E'' H'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] [TopologicalSpace H'']
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
  (K : ModelWithCorners ℂ E'' H'')
  {M N L : Type} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace L]
  [ChartedSpace H M] [ChartedSpace H' N] [ChartedSpace H'' L]

/-- The actual holomorphic coefficient maps compose through the canonical
composition isomorphism of the original literal restrictions. -/
theorem coefficientMap_comp (f : TopCat.of M ⟶ TopCat.of N)
    (hf : Topology.IsOpenEmbedding f) (hhol : ContMDiff I J ω f)
    (g : TopCat.of L ⟶ TopCat.of M) (hg : Topology.IsOpenEmbedding g)
    (hghol : ContMDiff K I ω g) :
    (Embedding.restriction g hg).map (coefficientMap I J f hf hhol) ≫
        coefficientMap K I g hg hghol =
      (Embedding.restrictionCompIso f hf g hg).hom.app
          (HolomorphicFunctionSheaf.additiveSheaf J N) ≫
        coefficientMap K J (g ≫ f) (hf.comp hg) (hhol.comp hghol) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change sectionPullback K I g hg hghol U.unop
      (sectionPullback I J f hf hhol ((Embedding.openImage g hg).obj U.unop) s) =
    sectionPullback K J (g ≫ f) (hf.comp hg) (hhol.comp hghol) U.unop
      (((Embedding.restrictionCompIso f hf g hg).hom.app
        (HolomorphicFunctionSheaf.additiveSheaf J N)).hom.app (op U.unop) s)
  rw [Embedding.restrictionCompIso_hom_app]
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The actual identity holomorphic coefficient map is the canonical
identity comparison for literal restriction of the original sheaf. -/
theorem coefficientMap_id :
    coefficientMap I I (𝟙 (TopCat.of M)) Topology.IsOpenEmbedding.id contMDiff_id =
      (Embedding.restrictionIdIso (TopCat.of M)).hom.app
        (HolomorphicFunctionSheaf.additiveSheaf I M) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change sectionPullback I I (𝟙 (TopCat.of M)) Topology.IsOpenEmbedding.id
      contMDiff_id U.unop s =
    ((Embedding.restrictionIdIso (TopCat.of M)).hom.app
      (HolomorphicFunctionSheaf.additiveSheaf I M)).hom.app (op U.unop) s
  rw [Embedding.restrictionIdIso_hom_app]
  apply ContMDiffMap.ext
  intro x
  rfl

end OpenClassRestriction.HolomorphicEmbedding
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
