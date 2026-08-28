import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicCohomologyBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicEmbeddingComposition
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingCohomologyComposition

/-!
# Composition of the original holomorphic cohomology pullbacks

The genuine degree-one Ext restriction is functorial through the actual
restriction isomorphisms. The original holomorphic coefficient maps
have exactly the matching composition formula. Thus native holomorphic
cohomology pullback composes and has the original identity map.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.HolomorphicCohomology

variable {E E' E'' H H' H'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] [TopologicalSpace H'']
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
  (K : ModelWithCorners ℂ E'' H'')
  {M N L : Type} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace L]
  [ChartedSpace H M] [ChartedSpace H' N] [ChartedSpace H'' L]

/-- Successive original holomorphic pullbacks in degree one equal
the genuine pullback along the actual composite map. -/
theorem pullback_comp (f : TopCat.of M ⟶ TopCat.of N)
    (hf : Topology.IsOpenEmbedding f) (hhol : ContMDiff I J ω f)
    (g : TopCat.of L ⟶ TopCat.of M) (hg : Topology.IsOpenEmbedding g)
    (hghol : ContMDiff K I ω g)
    (a : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf J N) 1) :
    pullback K I g hg hghol 1 (pullback I J f hf hhol 1 a) =
      pullback K J (g ≫ f) (hf.comp hg) (hhol.comp hghol) 1 a := by
  let φf := HolomorphicEmbedding.coefficientMap I J f hf hhol
  let φg := HolomorphicEmbedding.coefficientMap K I g hg hghol
  let φc := HolomorphicEmbedding.coefficientMap K J (g ≫ f) (hf.comp hg) (hhol.comp hghol)
  let β := Embedding.cohomologyMap f hf (HolomorphicFunctionSheaf.additiveSheaf J N) 1 a
  let γ := Embedding.cohomologyMap g hg
    ((Embedding.restriction f hf).obj (HolomorphicFunctionSheaf.additiveSheaf J N)) 1 β
  have hn := Embedding.cohomologyMap_naturality g hg φf 1 β
  have hc := HolomorphicEmbedding.coefficientMap_comp I J K f hf hhol g hg hghol
  exact (congrArg (CategoryTheory.Sheaf.H.map φg 1) hn).trans
    ((CategoryTheory.Sheaf.H.map_comp_apply ((Embedding.restriction g hg).map φf) φg γ).symm.trans
      ((congrArg (fun φ => CategoryTheory.Sheaf.H.map φ 1 γ) hc).trans
        ((CategoryTheory.Sheaf.H.map_comp_apply
          ((Embedding.restrictionCompIso f hf g hg).hom.app
            (HolomorphicFunctionSheaf.additiveSheaf J N)) φc γ).trans
          (congrArg (CategoryTheory.Sheaf.H.map φc 1)
            (Embedding.cohomologyMap_comp f hf g hg
              (HolomorphicFunctionSheaf.additiveSheaf J N) a)))))

/-- The original identity embedding acts as the identity on native
degree-one holomorphic cohomology. -/
theorem pullback_id
    (a : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 1) :
    pullback I I (𝟙 (TopCat.of M)) Topology.IsOpenEmbedding.id contMDiff_id 1 a = a := by
  exact (congrArg (fun φ => CategoryTheory.Sheaf.H.map φ 1
      (Embedding.cohomologyMap (𝟙 (TopCat.of M)) Topology.IsOpenEmbedding.id
        (HolomorphicFunctionSheaf.additiveSheaf I M) 1 a))
    (HolomorphicEmbedding.coefficientMap_id I)).trans
    (Embedding.cohomologyMap_id (TopCat.of M) (HolomorphicFunctionSheaf.additiveSheaf I M) a)

end OpenClassRestriction.HolomorphicCohomology
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
