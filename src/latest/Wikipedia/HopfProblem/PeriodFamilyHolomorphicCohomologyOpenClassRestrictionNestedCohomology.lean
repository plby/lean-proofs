import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedUnit
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingCohomologyBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionExtOneComparisonComposition

/-!
# The original cohomology-presheaf restriction under actual nested-open comparison

The genuine degree-one cohomology-presheaf map is precomposition by
the original free-open map. Its actual open comparison equals successive
exact restrictions through the original smaller open, followed by the
canonical restriction isomorphism. The endpoint identity is proved on
native universal sections; no higher-cohomology naturality is assumed.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicSheafCohomology
open CuspNormalization.SheafCohomologyFinitePushforward SheafHigherDirectImage.Sections

variable {X : TopCat.{0}} {U W : Opens X}

/-- Native cohomology-presheaf restriction is genuinely compatible with
the original open comparisons and the actual nested restriction functors. -/
theorem nestedCohomologyEquiv_restrict (h : U ≤ W)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (a : CategoryTheory.Sheaf.H'.{0} F 1 W) :
    CategoryTheory.Sheaf.H.map ((nestedRestrictionIso h).hom.app F) 1
        (Embedding.cohomologyMap (nestedInclusion h) (nestedEmbedding h)
          ((OpenRestriction.restriction W).obj F) 1
          (OpenRestriction.cohomologyEquiv W F 1 a)) =
      OpenRestriction.cohomologyEquiv U F 1
        ((CategoryTheory.Sheaf.cohomologyPresheaf F 1).map (homOfLE h).op a) := by
  have hc := @ExtOne.comparison_comp_natTrans
    (AbelianSheaf X) _ _ (abelianSheaf_hasExt X)
    (AbelianSheaf (TopCat.of W)) _ _ (abelianSheaf_hasExt (TopCat.of W))
    (AbelianSheaf (TopCat.of U)) _ _ (abelianSheaf_hasExt (TopCat.of U)) inferInstance
    (OpenRestriction.restriction W) (OpenRestriction.restriction_additive W)
    (OpenRestriction.restriction_preservesFiniteLimits W)
    (OpenRestriction.restriction_preservesFiniteColimits W)
    (Embedding.restriction (nestedInclusion h) (nestedEmbedding h))
    (Embedding.restriction_additive (nestedInclusion h) (nestedEmbedding h))
    (Embedding.restriction_preservesFiniteLimits (nestedInclusion h) (nestedEmbedding h))
    (Embedding.restriction_preservesFiniteColimits (nestedInclusion h) (nestedEmbedding h))
    (OpenRestriction.restriction U) (OpenRestriction.restriction_additive U)
    (OpenRestriction.restriction_preservesFiniteLimits U)
    (OpenRestriction.restriction_preservesFiniteColimits U)
    (nestedRestrictionIso h).hom (OpenRestriction.freeOpen W) F
    (integerSheaf (TopCat.of W)) (integerSheaf (TopCat.of U))
    (OpenRestriction.representingUnit W)
    (Embedding.integerUnit (nestedInclusion h) (nestedEmbedding h))
    (OpenRestriction.representingUnit U ≫
      (OpenRestriction.restriction U).map ((freeOpenFunctor X).map (homOfLE h)))
    (nested_representingUnit h) a
  have hp := @ExtOne.comparison_precompose
    (AbelianSheaf X) _ _ (abelianSheaf_hasExt X)
    (AbelianSheaf (TopCat.of U)) _ _ (abelianSheaf_hasExt (TopCat.of U))
    (OpenRestriction.restriction U) (OpenRestriction.restriction_additive U)
    (OpenRestriction.restriction_preservesFiniteLimits U)
    (OpenRestriction.restriction_preservesFiniteColimits U)
    (OpenRestriction.freeOpen U) (OpenRestriction.freeOpen W) (integerSheaf (TopCat.of U))
    (OpenRestriction.representingUnit U) ((freeOpenFunctor X).map (homOfLE h)) F 1 a
  exact hc.trans hp.symm

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
