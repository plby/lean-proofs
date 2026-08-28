import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionClass
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionCohomology

/-!
# Literal holomorphic Čech classes on the actual open submanifold

The genuine restricted coefficient sheaf is compared with the actual
holomorphic sheaf of the inherited open-submanifold atlas by the proved
literal flattening isomorphism. The original cohomology restriction
therefore carries an original Čech class to the class of its actual
restricted holomorphic functions. No separation or manifold hypothesis
beyond the native charted-space definitions is required here.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open HolomorphicSheafCohomology PeriodFamilyHigherDirectImage

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (A : Opens M) {ι : Type} {U : ι → Opens M}
  (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf I M) U)

/-- Actual section restriction followed by literal nested-domain
flattening gives a cocycle in the original open-submanifold holomorphic sheaf. -/
def holomorphicRestrictedCocycle :
    CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf I A)
      (restrictedCover (X := TopCat.of M) A U) :=
  HolomorphicPicard.Cech.mapCocycle (HolomorphicRestriction.sheafIso I A).hom
    (restrictedCocycle (X := TopCat.of M) A c)

/-- Each actual restricted holomorphic value is precisely the original
function evaluated at the same underlying ambient point. -/
theorem holomorphicRestrictedCocycle_value_apply (i j : ι)
    (x : ↥(restrictedCover (X := TopCat.of M) A U i ⊓
      restrictedCover (X := TopCat.of M) A U j)) :
    Subtype.val ((holomorphicRestrictedCocycle I A c).value i j :
      HolomorphicFunctionSheaf.Section I A
        (restrictedCover (X := TopCat.of M) A U i ⊓
          restrictedCover (X := TopCat.of M) A U j)) x =
      Subtype.val (c.value i j : HolomorphicFunctionSheaf.Section I M (U i ⊓ U j))
        ⟨x.val.val, x.property⟩ := rfl

/-- The original holomorphic open comparison carries the original
global Čech class to the actual class of its literal restricted functions. -/
theorem holomorphicCohomologyEquiv_restrictionMap_classOf
    (hU : ∀ x : M, ∃ i : ι, x ∈ U i) :
    HolomorphicRestriction.cohomologyEquiv I A 1
      (GlobalRestriction.restrictionMap (HolomorphicFunctionSheaf.additiveSheaf I M)
        A 1 (classOf c hU)) =
      classOf (holomorphicRestrictedCocycle I A c)
        (restrictedCover_covers (X := TopCat.of M) A hU) := by
  exact map_cohomologyEquiv_restrictionMap_classOf (X := TopCat.of M) A c hU
    (HolomorphicRestriction.sheafIso I A).hom

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
