import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionFamilyBasic

/-!
# An actual common refinement of the two original family lift covers

The inverse image of the original cover and the independently chosen
native cover of the restricted family are not identified. Their actual
intersections form a common cover. On each such open, both literal lifts
are continuous and project to the same original total-family map.
-/

noncomputable section

open Topology TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- Actual pairwise intersections of the pulled-back and native lift covers. -/
def familyCommonCover (P : HolomorphicPeriodMap V B) (A : Opens B) :
    (B × ComplexPlane₂) × (A × ComplexPlane₂) →
      Opens (Restriction.restrictedPeriods P A).TotalSpace :=
  fun k => familyPullbackCover P A k.1 ⊓
    Cocycle.coverOpen (Restriction.restrictedPeriods P A) k.2

/-- The two proved covers give a genuine common refinement, with no choice of identification. -/
theorem familyCommonCover_covers (P : HolomorphicPeriodMap V B) (A : Opens B)
    (x : (Restriction.restrictedPeriods P A).TotalSpace) :
    ∃ k, x ∈ familyCommonCover P A k := by
  obtain ⟨i, hi⟩ := familyPullbackCover_covers P A x
  obtain ⟨j, hj⟩ := Cocycle.coverOpen_covers (Restriction.restrictedPeriods P A) x
  exact ⟨(i, j), hi, hj⟩

/-- The original chosen lift, composed with the actual family inclusion. -/
def familyOriginalLift (P : HolomorphicPeriodMap V B) (A : Opens B)
    (k : (B × ComplexPlane₂) × (A × ComplexPlane₂)) :
    (Restriction.restrictedPeriods P A).TotalSpace → B × ComplexPlane₂ :=
  fun x => Cocycle.lift P k.1 (familyMap P A x)

/-- The independently chosen native lift, with only its base tag forgotten. -/
def familyNativeLift (P : HolomorphicPeriodMap V B) (A : Opens B)
    (k : (B × ComplexPlane₂) × (A × ComplexPlane₂)) :
    (Restriction.restrictedPeriods P A).TotalSpace → B × ComplexPlane₂ :=
  fun x => upstairsForget A (Cocycle.lift (Restriction.restrictedPeriods P A) k.2 x)

theorem familyOriginalLift_continuousAt (P : HolomorphicPeriodMap V B) (A : Opens B)
    (k : (B × ComplexPlane₂) × (A × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P A).TotalSpace}
    (hx : x ∈ familyCommonCover P A k) : ContinuousAt (familyOriginalLift P A k) x :=
  ((Cocycle.lift P k.1).continuousAt hx.1).comp (familyMap P A).hom.continuous.continuousAt

theorem familyNativeLift_continuousAt (P : HolomorphicPeriodMap V B) (A : Opens B)
    (k : (B × ComplexPlane₂) × (A × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P A).TotalSpace}
    (hx : x ∈ familyCommonCover P A k) : ContinuousAt (familyNativeLift P A k) x :=
  (upstairsForget_continuous A).continuousAt.comp
    ((Cocycle.lift (Restriction.restrictedPeriods P A) k.2).continuousAt hx.2)

theorem familyOriginalLift_project (P : HolomorphicPeriodMap V B) (A : Opens B)
    (k : (B × ComplexPlane₂) × (A × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P A).TotalSpace}
    (hx : x ∈ familyCommonCover P A k) :
    P.quotientMap (familyOriginalLift P A k x) = familyMap P A x :=
  Cocycle.project_lift P k.1 hx.1

theorem familyNativeLift_project (P : HolomorphicPeriodMap V B) (A : Opens B)
    (k : (B × ComplexPlane₂) × (A × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P A).TotalSpace}
    (hx : x ∈ familyCommonCover P A k) :
    P.quotientMap (familyNativeLift P A k x) = familyMap P A x := by
  exact congrArg (familyMap P A)
    (Cocycle.project_lift (Restriction.restrictedPeriods P A) k.2 hx.2)

/-- The original lift is an actual local lift of the original family map. -/
theorem familyOriginalLift_project_eventuallyEq (P : HolomorphicPeriodMap V B)
    (A : Opens B) (k : (B × ComplexPlane₂) × (A × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P A).TotalSpace}
    (hx : x ∈ familyCommonCover P A k) :
    (P.quotientMap ∘ familyOriginalLift P A k) =ᶠ[𝓝 x] familyMap P A := by
  filter_upwards [(familyCommonCover P A k).isOpen.mem_nhds hx] with y hy
  exact familyOriginalLift_project P A k hy

/-- The independent native lift is a local lift of that same original map. -/
theorem familyNativeLift_project_eventuallyEq (P : HolomorphicPeriodMap V B)
    (A : Opens B) (k : (B × ComplexPlane₂) × (A × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P A).TotalSpace}
    (hx : x ∈ familyCommonCover P A k) :
    (P.quotientMap ∘ familyNativeLift P A k) =ᶠ[𝓝 x] familyMap P A := by
  filter_upwards [(familyCommonCover P A k).isOpen.mem_nhds hx] with y hy
  exact familyNativeLift_project P A k hy

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
