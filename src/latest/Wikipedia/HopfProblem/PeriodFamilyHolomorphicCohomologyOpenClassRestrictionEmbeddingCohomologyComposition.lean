import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingCohomologyBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionExtOneComparisonComposition

/-!
# Genuine composition of native degree-one open-embedding restriction

The original exact restriction functors compose through their canonical
actual image-open isomorphism. Their native integer endpoints satisfy
the proved composition formula. Actual degree-one Ext functoriality
therefore yields composition and identity on the original cohomology.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.Embedding

open CuspNormalization.SheafCohomologyFinitePushforward

variable {S T X : TopCat.{0}}

/-- The canonical restriction composition isomorphism identifies
successive native degree-one restrictions with the actual composite map. -/
theorem cohomologyMap_comp (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)
    (g : S ⟶ T) (hg : Topology.IsOpenEmbedding g)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (a : CategoryTheory.Sheaf.H.{0} F 1) :
    CategoryTheory.Sheaf.H.map ((restrictionCompIso f hf g hg).hom.app F) 1
        (cohomologyMap g hg ((restriction f hf).obj F) 1 (cohomologyMap f hf F 1 a)) =
      cohomologyMap (g ≫ f) (hf.comp hg) F 1 a :=
  @ExtOne.comparison_comp_natTrans
    (AbelianSheaf X) _ _ (abelianSheaf_hasExt X)
    (AbelianSheaf T) _ _ (abelianSheaf_hasExt T)
    (AbelianSheaf S) _ _ (abelianSheaf_hasExt S) inferInstance
    (restriction f hf) (restriction_additive f hf)
    (restriction_preservesFiniteLimits f hf) (restriction_preservesFiniteColimits f hf)
    (restriction g hg) (restriction_additive g hg)
    (restriction_preservesFiniteLimits g hg) (restriction_preservesFiniteColimits g hg)
    (restriction (g ≫ f) (hf.comp hg)) (restriction_additive (g ≫ f) (hf.comp hg))
    (restriction_preservesFiniteLimits (g ≫ f) (hf.comp hg))
    (restriction_preservesFiniteColimits (g ≫ f) (hf.comp hg))
    (restrictionCompIso f hf g hg).hom
    (integerSheaf X) F (integerSheaf T) (integerSheaf S)
    (integerUnit f hf) (integerUnit g hg) (integerUnit (g ≫ f) (hf.comp hg))
    (integerUnit_comp f hf g hg) a

/-- The actual identity restriction induces the identity on original
degree-one cohomology under its canonical sheaf comparison. -/
theorem cohomologyMap_id (X : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (a : CategoryTheory.Sheaf.H.{0} F 1) :
    CategoryTheory.Sheaf.H.map ((restrictionIdIso X).hom.app F) 1
        (cohomologyMap (𝟙 X) Topology.IsOpenEmbedding.id F 1 a) = a :=
  @ExtOne.comparison_natTrans_id
    (AbelianSheaf X) _ _ (abelianSheaf_hasExt X) inferInstance
    (restriction (𝟙 X) Topology.IsOpenEmbedding.id)
    (restriction_additive (𝟙 X) Topology.IsOpenEmbedding.id)
    (restriction_preservesFiniteLimits (𝟙 X) Topology.IsOpenEmbedding.id)
    (restriction_preservesFiniteColimits (𝟙 X) Topology.IsOpenEmbedding.id)
    (restrictionIdIso X).hom (integerSheaf X) F
    (integerUnit (𝟙 X) Topology.IsOpenEmbedding.id) (integerUnit_id X) a

end OpenClassRestriction.Embedding
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
