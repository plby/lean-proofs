import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionLifts
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionUnit
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingClass

/-!
# A genuine map from the restricted Čech extension to the exact restriction

The original restricted local degree-one sections define an actual
glued map from the extension of the literal restricted cocycle to the
exact open restriction of the original extension. Its left endpoint is
the identity of the original restricted coefficient sheaf. Its right
endpoint is the original integer restriction unit, whose section formula
has been proved on every original open. No endpoint isomorphism is assumed.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicFunctionSheaf.SphereH1
open HolomorphicSheafCohomology
open HolomorphicPicard.CechExtension

variable {X : TopCat.{0}} (A : Opens X)
  {F : TopCat.Sheaf AddCommGrpCat.{0} X} {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U) (hU : ∀ x : X, ∃ i : ι, x ∈ U i)

/-- The actual local gluing comparison between the two original
extension sheaves on the actual open subspace. -/
def restrictedExtensionMap :
    extensionSheaf (restrictedCocycle A c) ⟶
      (OpenRestriction.restriction A).obj (extensionSheaf c) :=
  comparison (restrictedCocycle A c) (restrictedCover_covers A hU)
    ((OpenRestriction.restriction A).map (inclusion c)) (restrictedLocalSection A c)
    (restrictedLocalSection_difference A c)

/-- The left endpoint is the actual restricted coefficient inclusion. -/
theorem inclusion_restrictedExtensionMap :
    inclusion (restrictedCocycle A c) ≫ restrictedExtensionMap A c hU =
      (OpenRestriction.restriction A).map (inclusion c) :=
  inclusion_comparison (restrictedCocycle A c) (restrictedCover_covers A hU)
    ((OpenRestriction.restriction A).map (inclusion c)) (restrictedLocalSection A c)
    (restrictedLocalSection_difference A c)

/-- Exact open restriction retains the actual zero composite of the
original coefficient inclusion and the original degree projection. -/
theorem restricted_inclusion_projection :
    (OpenRestriction.restriction A).map (inclusion c) ≫
      (OpenRestriction.restriction A).map (projection c) = 0 := by
  exact ((OpenRestriction.restriction A).map_comp (inclusion c) (projection c)).symm.trans
    ((congrArg (OpenRestriction.restriction A).map (inclusion_projection c)).trans
      ((OpenRestriction.restriction A).map_zero _ _))

/-- Each literal local lift has the degree specified by the genuine
integer endpoint, by its proved actual constant-section formula. -/
theorem restrictedLocalSection_projection_unit (i : ι) :
    ((OpenRestriction.restriction A).map (projection c)).hom.app
        (op (restrictedCover A U i)) (restrictedLocalSection A c i) =
      (integerRestrictionUnit A).hom.app (op (restrictedCover A U i))
        ((degreeUnit (TopCat.of A)).app (op (restrictedCover A U i)) (ULift.up (1 : ℤ))) :=
  (restrictedLocalSection_projection A c i).trans
    (integerRestrictionUnit_degreeUnit_app A (restrictedCover A U i) (ULift.up (1 : ℤ))).symm

/-- The genuine extension map has the original integer restriction
unit as its right endpoint. -/
theorem restrictedExtensionMap_projection :
    restrictedExtensionMap A c hU ≫ (OpenRestriction.restriction A).map (projection c) =
      projection (restrictedCocycle A c) ≫ integerRestrictionUnit A :=
  CechConnecting.comparison_projection_map (restrictedCocycle A c)
    (restrictedCover_covers A hU) ((OpenRestriction.restriction A).map (inclusion c))
    ((OpenRestriction.restriction A).map (projection c)) (integerRestrictionUnit A)
    (restricted_inclusion_projection A c) (restrictedLocalSection A c)
    (restrictedLocalSection_projection_unit A c) (restrictedLocalSection_difference A c)

/-- The actual map of the original short complexes, with identity
coefficient endpoint and the proved original integer endpoint. -/
def restrictedComplexMap :
    complex (restrictedCocycle A c) ⟶ (complex c).map (OpenRestriction.restriction A) :=
  CechConnecting.comparisonComplexMap ((complex c).map (OpenRestriction.restriction A))
    (restrictedCocycle A c) (restrictedCover_covers A hU) (integerRestrictionUnit A)
    (restrictedLocalSection A c) (restrictedLocalSection_projection_unit A c)
    (restrictedLocalSection_difference A c)

@[simp] theorem restrictedComplexMap_left :
    (restrictedComplexMap A c hU).τ₁ = 𝟙 ((OpenRestriction.restriction A).obj F) := rfl

@[simp] theorem restrictedComplexMap_right :
    (restrictedComplexMap A c hU).τ₃ = integerRestrictionUnit A := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
