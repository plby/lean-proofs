import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedPeriodCocycleBasic

/-!
# A genuine common cover for nested-family period cocycles

The larger-family lift cover is pulled back literally. Its intersections
with the independently chosen smaller-family lift cover form a common
refinement. Both local lifts project to the same original nested inclusion.
-/

noncomputable section

open Topology TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.NestedPeriodCocycle

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  {U W : Opens B}

/-- Actual intersections, with one index from each independently chosen cover. -/
def commonCover (P : HolomorphicPeriodMap V B) (h : U ≤ W) :
    (W × ComplexPlane₂) × (U × ComplexPlane₂) →
      Opens (Restriction.restrictedPeriods P U).TotalSpace :=
  fun k => pullbackCover P h k.1 ⊓
    Cocycle.coverOpen (Restriction.restrictedPeriods P U) k.2

/-- Both original covers contribute a genuine covering index at every point. -/
theorem commonCover_covers (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (x : (Restriction.restrictedPeriods P U).TotalSpace) :
    ∃ k, x ∈ commonCover P h k := by
  obtain ⟨i, hi⟩ := pullbackCover_covers P h x
  obtain ⟨j, hj⟩ := Cocycle.coverOpen_covers (Restriction.restrictedPeriods P U) x
  exact ⟨(i, j), hi, hj⟩

/-- The larger-family lift composed with the actual nested inclusion. -/
def originalLift (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (k : (W × ComplexPlane₂) × (U × ComplexPlane₂)) :
    (Restriction.restrictedPeriods P U).TotalSpace → W × ComplexPlane₂ :=
  fun x => Cocycle.lift (Restriction.restrictedPeriods P W) k.1 (familyMap P h x)

/-- The independently chosen smaller-family lift, included upstairs. -/
def nativeLift (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (k : (W × ComplexPlane₂) × (U × ComplexPlane₂)) :
    (Restriction.restrictedPeriods P U).TotalSpace → W × ComplexPlane₂ :=
  fun x => upstairsInclusion h (Cocycle.lift (Restriction.restrictedPeriods P U) k.2 x)

theorem originalLift_continuousAt (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (k : (W × ComplexPlane₂) × (U × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P U).TotalSpace}
    (hx : x ∈ commonCover P h k) : ContinuousAt (originalLift P h k) x :=
  ((Cocycle.lift (Restriction.restrictedPeriods P W) k.1).continuousAt hx.1).comp
    (familyMap P h).hom.continuous.continuousAt

theorem nativeLift_continuousAt (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (k : (W × ComplexPlane₂) × (U × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P U).TotalSpace}
    (hx : x ∈ commonCover P h k) : ContinuousAt (nativeLift P h k) x :=
  (upstairsInclusion_continuous h).continuousAt.comp
    ((Cocycle.lift (Restriction.restrictedPeriods P U) k.2).continuousAt hx.2)

theorem originalLift_project (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (k : (W × ComplexPlane₂) × (U × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P U).TotalSpace}
    (hx : x ∈ commonCover P h k) :
    (Restriction.restrictedPeriods P W).quotientMap (originalLift P h k x) =
      familyMap P h x :=
  Cocycle.project_lift (Restriction.restrictedPeriods P W) k.1 hx.1

theorem nativeLift_project (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (k : (W × ComplexPlane₂) × (U × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P U).TotalSpace}
    (hx : x ∈ commonCover P h k) :
    (Restriction.restrictedPeriods P W).quotientMap (nativeLift P h k x) =
      familyMap P h x := by
  exact congrArg (familyMap P h)
    (Cocycle.project_lift (Restriction.restrictedPeriods P U) k.2 hx.2)

/-- The pulled-back lift is locally a lift of the genuine nested inclusion. -/
theorem originalLift_project_eventuallyEq (P : HolomorphicPeriodMap V B)
    (h : U ≤ W) (k : (W × ComplexPlane₂) × (U × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P U).TotalSpace}
    (hx : x ∈ commonCover P h k) :
    ((Restriction.restrictedPeriods P W).quotientMap ∘ originalLift P h k) =ᶠ[𝓝 x]
      familyMap P h := by
  filter_upwards [(commonCover P h k).isOpen.mem_nhds hx] with y hy
  exact originalLift_project P h k hy

/-- The independent native lift is a lift of the same nested inclusion. -/
theorem nativeLift_project_eventuallyEq (P : HolomorphicPeriodMap V B)
    (h : U ≤ W) (k : (W × ComplexPlane₂) × (U × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P U).TotalSpace}
    (hx : x ∈ commonCover P h k) :
    ((Restriction.restrictedPeriods P W).quotientMap ∘ nativeLift P h k) =ᶠ[𝓝 x]
      familyMap P h := by
  filter_upwards [(commonCover P h k).isOpen.mem_nhds hx] with y hy
  exact nativeLift_project P h k hy

end OpenClassRestriction.NestedPeriodCocycle
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
