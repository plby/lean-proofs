import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicCohomologyBasic

/-!
# Coefficient naturality of genuine holomorphic open pullback

An actual coefficient square on the original holomorphic sheaves gives
the corresponding square on their native cohomology in every degree.
The map is the original exact-restriction Ext map followed by literal
holomorphic section pullback, without a cohomology-coordinate model.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction

open PeriodFamilyHolomorphicCohomology.OpenClassRestriction

variable {E E' H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  (f : TopCat.of M ⟶ TopCat.of N) (hf : Topology.IsOpenEmbedding f)
  (hhol : ContMDiff I J ω f)

/-- Genuine holomorphic pullback respects an actual coefficient square, in every degree. -/
theorem holomorphicPullback_map
    (a : HolomorphicFunctionSheaf.additiveSheaf J N ⟶
      HolomorphicFunctionSheaf.additiveSheaf J N)
    (b : HolomorphicFunctionSheaf.additiveSheaf I M ⟶
      HolomorphicFunctionSheaf.additiveSheaf I M)
    (hab : (Embedding.restriction f hf).map a ≫
        HolomorphicEmbedding.coefficientMap I J f hf hhol =
      HolomorphicEmbedding.coefficientMap I J f hf hhol ≫ b)
    (q : ℕ) (x : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf J N) q) :
    HolomorphicCohomology.pullback I J f hf hhol q (CategoryTheory.Sheaf.H.map a q x) =
      CategoryTheory.Sheaf.H.map b q (HolomorphicCohomology.pullback I J f hf hhol q x) := by
  let φ := HolomorphicEmbedding.coefficientMap I J f hf hhol
  let y := Embedding.cohomologyMap f hf (HolomorphicFunctionSheaf.additiveSheaf J N) q x
  have hn := Embedding.cohomologyMap_naturality f hf a q x
  have hl := CategoryTheory.Sheaf.H.map_comp_apply ((Embedding.restriction f hf).map a) φ y
  have hr := CategoryTheory.Sheaf.H.map_comp_apply φ b y
  have hm := congrArg (fun k : (Embedding.restriction f hf).obj
      (HolomorphicFunctionSheaf.additiveSheaf J N) ⟶
        HolomorphicFunctionSheaf.additiveSheaf I M => CategoryTheory.Sheaf.H.map k q y) hab
  exact (congrArg (CategoryTheory.Sheaf.H.map φ q) hn).trans
    (hl.symm.trans (hm.trans hr))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction
