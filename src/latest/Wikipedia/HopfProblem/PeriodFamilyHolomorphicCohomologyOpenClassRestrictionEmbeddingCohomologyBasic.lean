import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingUnit
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionExtOneComparison

/-!
# Actual native cohomology restriction along an open embedding

The map on the original Ext-defined groups is the actual exact
restriction-functor map preceded by the genuine constant integer
endpoint. For the original open-subspace inclusion, it agrees with
the already constructed global-to-neighborhood restriction followed
by the original open cohomology comparison.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.Embedding

open CuspNormalization.SheafCohomologyFinitePushforward
open HolomorphicSheafCohomology PeriodFamilyHigherDirectImage

variable {T X : TopCat.{0}} (f : T ⟶ X) (hf : Topology.IsOpenEmbedding f)

/-- The original exact-functor Ext map with its actual integer endpoint. -/
def cohomologyMap (F : TopCat.Sheaf AddCommGrpCat.{0} X) (q : ℕ) :
    CategoryTheory.Sheaf.H.{0} F q →+
      CategoryTheory.Sheaf.H.{0} ((restriction f hf).obj F) q :=
  ExtComparison.comparison (restriction f hf) (integerUnit f hf) F q

/-- Actual restriction commutes with original coefficient sheaf maps in every degree. -/
theorem cohomologyMap_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (g : F ⟶ G) (q : ℕ) (a : CategoryTheory.Sheaf.H.{0} F q) :
    cohomologyMap f hf G q (CategoryTheory.Sheaf.H.map g q a) =
      CategoryTheory.Sheaf.H.map ((restriction f hf).map g) q (cohomologyMap f hf F q a) :=
  @ExtComparison.comparison_naturality
    (AbelianSheaf X) _ _ (AbelianSheaf T) _ _
    (restriction f hf) (restriction_additive f hf)
    (restriction_preservesFiniteLimits f hf) (restriction_preservesFiniteColimits f hf)
    (abelianSheaf_hasExt X) (abelianSheaf_hasExt T)
    (integerSheaf X) (integerSheaf T) (integerUnit f hf) F G g q a

/-- For the actual open inclusion, this native Ext map is exactly
the original global restriction followed by the original open comparison. -/
theorem cohomologyMap_inclusion (A : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (q : ℕ) (a : CategoryTheory.Sheaf.H.{0} F q) :
    cohomologyMap (OpenRestriction.inclusion A) (OpenRestriction.inclusion_isOpenEmbedding A)
        F q a =
      OpenRestriction.cohomologyEquiv A F q (GlobalRestriction.restrictionMap F A q a) := by
  exact (congrArg (fun η : integerSheaf (TopCat.of A) ⟶
      (OpenRestriction.restriction A).obj (integerSheaf X) =>
      ExtComparison.comparison (OpenRestriction.restriction A) η F q a)
    (ImageInteger.unit_openImage A)).trans
      (cohomologyEquiv_restrictionMap A F q a).symm

end OpenClassRestriction.Embedding
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
