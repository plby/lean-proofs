import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicEmbeddingBasic

/-!
# The original holomorphic coefficient map for an open embedding

The actual all-open complex-algebra pullbacks form a morphism from
literal restriction of the original target holomorphic sheaf to the
original source holomorphic sheaf. Both sheaves retain the given atlases.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.HolomorphicEmbedding

variable {E E' H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  (f : TopCat.of M ⟶ TopCat.of N) (hf : Topology.IsOpenEmbedding f)
  (hhol : ContMDiff I J ω f)

include hhol

/-- The genuine coefficient morphism induced by literal holomorphic
composition on every original open. -/
def coefficientMap :
    (Embedding.restriction f hf).obj (HolomorphicFunctionSheaf.additiveSheaf J N) ⟶
      HolomorphicFunctionSheaf.additiveSheaf I M where
  hom :=
    { app U := AddCommGrpCat.ofHom (sectionPullback I J f hf hhol U.unop).toAddMonoidHom
      naturality U W h := by
        apply ConcreteCategory.hom_ext
        intro s
        exact (sectionPullback_restrict I J f hf hhol (leOfHom h.unop) s).symm }

/-- The actual sheaf-map component is precisely the constructed algebra pullback. -/
@[simp] theorem coefficientMap_app (U : Opens M)
    (s : HolomorphicFunctionSheaf.Section J N ((Embedding.openImage f hf).obj U)) :
    (coefficientMap I J f hf hhol).hom.app (op U) s =
      sectionPullback I J f hf hhol U s := rfl

/-- Its pointwise value is the original function at the original mapped point. -/
@[simp] theorem coefficientMap_app_apply (U : Opens M)
    (s : HolomorphicFunctionSheaf.Section J N ((Embedding.openImage f hf).obj U)) (x : U) :
    Subtype.val ((coefficientMap I J f hf hhol).hom.app (op U) s :
      HolomorphicFunctionSheaf.Section I M U) x = s (imageMap f hf U x) := rfl

end OpenClassRestriction.HolomorphicEmbedding
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
