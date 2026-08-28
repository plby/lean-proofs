import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionMaps
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClassNaturality

/-!
# Genuine Čech extension classes commute with actual open restriction

The original global cohomology class, restricted by the canonical
free-open map and then compared with cohomology of the actual restricted
sheaf, is the genuine extension class of the literal restricted cocycle.
The proof uses the actual map of short complexes, exact open restriction,
and the proved original integer endpoint. No comparison is assumed, and
no closedness, compactness, or separation hypothesis is needed.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open HolomorphicSheafCohomology PeriodFamilyHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward

variable {X : TopCat.{0}} (A : Opens X)
  {F : TopCat.Sheaf AddCommGrpCat.{0} X} {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U) (hU : ∀ x : X, ∃ i : ι, x ∈ U i)

/-- The original free-open restriction of the genuine extension class
is the genuine class of the literal cocycle on the original open subspace. -/
theorem cohomologyEquiv_restrictionMap_classOf :
    OpenRestriction.cohomologyEquiv A F 1
      (GlobalRestriction.restrictionMap F A 1 (classOf c hU)) =
    classOf (restrictedCocycle A c) (restrictedCover_covers A hU) := by
  have hmap := @Ext.mapExactFunctor_extClass
    (AbelianSheaf X) _ _ (AbelianSheaf (TopCat.of A)) _ _
    (OpenRestriction.restriction A) (OpenRestriction.restriction_additive A)
    (OpenRestriction.restriction_preservesFiniteLimits A)
    (OpenRestriction.restriction_preservesFiniteColimits A)
    (abelianSheaf_hasExt X) (abelianSheaf_hasExt (TopCat.of A))
    (complex c) (complex_shortExact c hU)
  have hclass := CechConnecting.classOf_eq_connecting
    ((complex c).map (OpenRestriction.restriction A))
    (restrictedCocycle A c) (restrictedCover_covers A hU) (integerRestrictionUnit A)
    (restrictedLocalSection A c) (restrictedLocalSection_projection_unit A c)
    (restrictedLocalSection_difference A c)
    ((complex_shortExact c hU).map_of_exact (OpenRestriction.restriction A))
  exact (cohomologyEquiv_restrictionMap A F 1 (classOf c hU)).trans
    ((congrArg (fun a => (Ext.mk₀ (integerRestrictionUnit A)).comp a (zero_add 1)) hmap).trans
      hclass.symm)

/-- The original neighborhood cohomology value itself is identified
with the genuine restricted extension class, through the proved comparison. -/
theorem restrictionMap_classOf :
    GlobalRestriction.restrictionMap F A 1 (classOf c hU) =
      (OpenRestriction.cohomologyEquiv A F 1).symm
        (classOf (restrictedCocycle A c) (restrictedCover_covers A hU)) := by
  apply (OpenRestriction.cohomologyEquiv A F 1).injective
  exact (cohomologyEquiv_restrictionMap_classOf A c hU).trans
    ((OpenRestriction.cohomologyEquiv A F 1).apply_symm_apply _).symm

/-- After any actual coefficient morphism on the original open
subspace, restriction is still represented by the literal mapped cocycle. -/
theorem map_cohomologyEquiv_restrictionMap_classOf
    {G : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of A)}
    (g : (OpenRestriction.restriction A).obj F ⟶ G) :
    CategoryTheory.Sheaf.H.map g 1
        (OpenRestriction.cohomologyEquiv A F 1
          (GlobalRestriction.restrictionMap F A 1 (classOf c hU))) =
      classOf (HolomorphicPicard.Cech.mapCocycle g (restrictedCocycle A c))
        (restrictedCover_covers A hU) := by
  rw [cohomologyEquiv_restrictionMap_classOf]
  exact HolomorphicPicard.CechExtension.classOf_naturality g
    (restrictedCocycle A c) (restrictedCover_covers A hU)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
