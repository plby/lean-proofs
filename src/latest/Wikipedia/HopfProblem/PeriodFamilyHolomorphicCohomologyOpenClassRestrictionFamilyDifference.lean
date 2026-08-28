import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionFamilyCover
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionPrimitiveDifference
import Wikipedia.HopfProblem.HolomorphicPicardCechRefinement

/-!
# The actual holomorphic change of primitive on the common family cover

The original pulled-back lift and the independently chosen native lift
project to the same original total-family point. Their primitive
difference is locally a fixed original lattice character, hence is a
genuine holomorphic function. Its literal local coboundary compares the
two actual refined period cocycles, keeping their first-minus-second sign.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open PeriodFamilyHigherDirectImage HolomorphicFunctionSheaf.SphereH1

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The literal original primitive minus the independent native primitive. -/
def familyDifference (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) (k : (B × ComplexPlane₂) × (A × ComplexPlane₂))
    (x : (Restriction.restrictedPeriods P A).TotalSpace) : ℂ :=
  Cocycle.primitive P a (familyOriginalLift P A k x) -
    Cocycle.primitive P a (familyNativeLift P A k x)

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual change of primitive is holomorphic on every common-cover open. -/
theorem familyDifference_holomorphicAt (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) (k : (B × ComplexPlane₂) × (A × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P A).TotalSpace}
    (hx : x ∈ familyCommonCover P A k) :
    letI := (Restriction.restrictedPeriods P A).totalChartedSpace
    ContMDiffAt IT 𝓘(ℂ) ω (familyDifference P A a k) x := by
  let := (Restriction.restrictedPeriods P A).totalChartedSpace
  let := P.totalChartedSpace
  exact PrimitiveDifference.difference_holomorphicAt P a (familyMap P A)
    (familyOriginalLift P A k) (familyNativeLift P A k)
    (familyOriginalLift_continuousAt P A k hx) (familyNativeLift_continuousAt P A k hx)
    (familyOriginalLift_project_eventuallyEq P A k hx)
    (familyNativeLift_project_eventuallyEq P A k hx)
    (familyMap_holomorphic P A).contMDiffAt

/-- A genuine native holomorphic section of the original restricted total family. -/
def familyDifferenceSection (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) (k : (B × ComplexPlane₂) × (A × ComplexPlane₂)) :
    Cocycle.NativeSection (Restriction.restrictedPeriods P A) (familyCommonCover P A k) := by
  letI := (Restriction.restrictedPeriods P A).totalChartedSpace
  refine ⟨fun x => familyDifference P A a k x, ?_⟩
  intro x
  exact (familyDifference_holomorphicAt P A a k x.property).comp x (contMDiff_subtype_val x)

/-- Its values are exactly the two original primitive functions, not a chosen extension. -/
theorem familyDifferenceSection_apply (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) (k : (B × ComplexPlane₂) × (A × ComplexPlane₂))
    (x : familyCommonCover P A k) :
    familyDifferenceSection P A a k x =
      Cocycle.primitive P a (Cocycle.lift P k.1 (familyMap P A x)) -
        Cocycle.primitive (Restriction.restrictedPeriods P A) (restrictCoefficients A a)
          (Cocycle.lift (Restriction.restrictedPeriods P A) k.2 x) := rfl

/-- The actual pulled-back cocycle restricted to the common refinement. -/
def familyCommonPullbackCocycle (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) :
    CechOneCocycle (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P A))
      (familyCommonCover P A) :=
  HolomorphicPicard.Cech.refinement _ Prod.fst (fun _ => inf_le_left)
    (familyPullbackCocycle P A a)

/-- The independently reconstructed native cocycle on that same common refinement. -/
def familyCommonNativeCocycle (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) :
    CechOneCocycle (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P A))
      (familyCommonCover P A) :=
  HolomorphicPicard.Cech.refinement _ Prod.snd (fun _ => inf_le_right)
    (Cocycle.cocycle (Restriction.restrictedPeriods P A) (restrictCoefficients A a))

/-- The actual holomorphic zero cochain supplied by the change of local primitive. -/
def familyComparisonCochain (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) :
    HolomorphicPicard.Cech.ZeroCochain
      (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P A)) (familyCommonCover P A) :=
  familyDifferenceSection P A a

/-- Literal telescoping identifies the difference of the actual refined
cocycles with the genuine local holomorphic coboundary. -/
theorem familyCommonCocycle_sub_eq_coboundary (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) :
    familyCommonPullbackCocycle P A a - familyCommonNativeCocycle P A a =
      HolomorphicPicard.Cech.coboundary
        (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P A))
        (familyCommonCover P A) (familyComparisonCochain P A a) := by
  let := (Restriction.restrictedPeriods P A).totalChartedSpace
  apply HolomorphicPicard.Cech.cocycle_ext
  intro k l
  apply ContMDiffMap.ext
  intro x
  change (Cocycle.primitive P a (familyOriginalLift P A k x) -
      Cocycle.primitive P a (familyOriginalLift P A l x)) -
    (Cocycle.primitive P a (familyNativeLift P A k x) -
      Cocycle.primitive P a (familyNativeLift P A l x)) =
    (Cocycle.primitive P a (familyOriginalLift P A k x) -
      Cocycle.primitive P a (familyNativeLift P A k x)) -
    (Cocycle.primitive P a (familyOriginalLift P A l x) -
      Cocycle.primitive P a (familyNativeLift P A l x))
  abel

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
