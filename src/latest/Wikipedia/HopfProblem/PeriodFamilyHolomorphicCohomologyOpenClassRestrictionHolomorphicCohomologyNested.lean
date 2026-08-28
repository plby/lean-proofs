import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicCohomologyBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicEmbeddingNested
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedCohomology

/-!
# Native holomorphic open comparison commutes with nested restriction

The original cohomology-presheaf restriction is identified with the
genuine pullback through the smaller original open. The comparison
uses the proved native free-open endpoint diagram and the literal
holomorphic coefficient square; it introduces no cohomology model.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.HolomorphicCohomology

open HolomorphicSheafCohomology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {U W : Opens M}

/-- The original holomorphic comparison for native open cohomology
intertwines the actual cohomology-presheaf restriction with genuine
holomorphic pullback through the nested original opens. -/
theorem pullback_nested (h : U ≤ W)
    (a : CategoryTheory.Sheaf.H'.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 1 W) :
    pullback I I (nestedInclusion (X := TopCat.of M) h)
        (nestedEmbedding (X := TopCat.of M) h) (contMDiff_inclusion h) 1
        (HolomorphicRestriction.cohomologyEquiv I W 1 a) =
      HolomorphicRestriction.cohomologyEquiv I U 1
        ((CategoryTheory.Sheaf.cohomologyPresheaf
          (HolomorphicFunctionSheaf.additiveSheaf I M) 1).map (homOfLE h).op a) := by
  let r := nestedInclusion (X := TopCat.of M) h
  let hr := nestedEmbedding (X := TopCat.of M) h
  let F := HolomorphicFunctionSheaf.additiveSheaf I M
  let φW := (HolomorphicRestriction.sheafIso I W).hom
  let φU := (HolomorphicRestriction.sheafIso I U).hom
  let φr := HolomorphicEmbedding.coefficientMap I I r hr (contMDiff_inclusion h)
  let β := OpenRestriction.cohomologyEquiv (X := TopCat.of M) W F 1 a
  let γ := Embedding.cohomologyMap r hr ((OpenRestriction.restriction W).obj F) 1 β
  have hn := Embedding.cohomologyMap_naturality r hr φW 1 β
  have hc := HolomorphicEmbedding.coefficientMap_nested I h
  exact (congrArg (CategoryTheory.Sheaf.H.map φr 1) hn).trans
    ((CategoryTheory.Sheaf.H.map_comp_apply ((Embedding.restriction r hr).map φW) φr γ).symm.trans
      ((congrArg (fun φ => CategoryTheory.Sheaf.H.map φ 1 γ) hc).trans
        ((CategoryTheory.Sheaf.H.map_comp_apply
          ((nestedRestrictionIso (X := TopCat.of M) h).hom.app F) φU γ).trans
          (congrArg (CategoryTheory.Sheaf.H.map φU 1)
            (nestedCohomologyEquiv_restrict (X := TopCat.of M) h F a)))))

end OpenClassRestriction.HolomorphicCohomology
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
