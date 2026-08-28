import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverCech
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverMayerVietoris
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverHigher

/-!
# Genuine H¹ and H² vanishing from literal three-chart section equations

The original Mayer--Vietoris sequence is applied to `U₀ ∪ U₁` and `U₂`.
The proved actual connecting-map comparison supplies exactly the
injectivity and surjectivity required in its low-degree terms.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
  (U : Fin 3 → Opens X)

theorem firstUnionRestriction_injective (hOne : CechOneExact F U)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 0))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 1))] :
    Function.Injective (cohomologyRestrict F 1
      (show firstUnion U ⊓ U 2 ≤ firstUnion U from inf_le_left)) :=
  cohomologyRestrict_injective_of_composite F 1 (firstUnion_inf U).ge inf_le_left
    (unionOverlapRestriction_injective F U hOne)

theorem firstUnionRestriction_surjective (hTwo : CechTwoSurjective F U)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 0 ⊓ U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 1 ⊓ U 2))] :
    Function.Surjective (cohomologyRestrict F 1
      (show firstUnion U ⊓ U 2 ≤ firstUnion U from inf_le_left)) :=
  cohomologyRestrict_surjective_of_composite F 1 (firstUnion_inf U).ge
    (firstUnion_inf U).le inf_le_left (unionOverlapRestriction_surjective F U hTwo)

/-- Literal one-cocycle exactness and chart H¹ vanishing give true H¹
vanishing on the actual union; pair acyclicity is not needed in degree one. -/
theorem cover_one_subsingleton (hOne : CechOneExact F U)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 0))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 1))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 2))] :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (coverOpen U)) :=
  union_one_subsingleton_of_maps F (firstUnion U) (U 2)
    (MayerVietoris.restrictionDifference_zero_surjective F (firstUnion U) (U 2)
      (union_sectionsDifference_surjective F U hOne))
    (restrictionDifference_injective_of_left F (firstUnion U) (U 2) 1
      (firstUnionRestriction_injective F U hOne))

/-- Literal triple-section surjectivity and the relevant actual
chart/pair vanishings give true degree-two vanishing on the actual union. -/
theorem cover_two_subsingleton (hTwo : CechTwoSurjective F U)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 2 (U 0))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 2 (U 1))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 2 (U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 0 ⊓ U 1))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 0 ⊓ U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 1 ⊓ U 2))] :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F 2 (coverOpen U)) := by
  have := firstUnion_higher_subsingleton F U 0
  exact union_successor_subsingleton_of_difference F (firstUnion U) (U 2) 1
    (restrictionDifference_surjective_of_left F (firstUnion U) (U 2) 1
      (firstUnionRestriction_surjective F U hTwo))

/-- For a genuine three-open cover this is vanishing of the original
global Ext-defined H¹, not an assumed Čech comparison. -/
theorem sheaf_one_subsingleton (hcover : coverOpen U = ⊤) (hOne : CechOneExact F U)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 0))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 1))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 2))] :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F 1) :=
  MayerVietoris.sheaf_subsingleton_of_union F (firstUnion U) (U 2) hcover 1
    (cover_one_subsingleton F U hOne)

/-- The corresponding actual global H² vanishing theorem. -/
theorem sheaf_two_subsingleton (hcover : coverOpen U = ⊤) (hTwo : CechTwoSurjective F U)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 2 (U 0))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 2 (U 1))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 2 (U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 0 ⊓ U 1))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 0 ⊓ U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 1 ⊓ U 2))] :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F 2) :=
  MayerVietoris.sheaf_subsingleton_of_union F (firstUnion U) (U 2) hcover 2
    (cover_two_subsingleton F U hTwo)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover
