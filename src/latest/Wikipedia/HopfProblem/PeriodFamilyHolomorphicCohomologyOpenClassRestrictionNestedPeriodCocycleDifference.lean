import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedPeriodCocycleCover
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionPrimitiveDifference
import Wikipedia.HopfProblem.HolomorphicPicardCechRefinement

/-!
# The holomorphic change of primitive for nested period families

On the actual common cover, the two continuous lifts project to the same
point of the larger restricted family. Their primitive difference is
locally a fixed lattice character. The resulting native holomorphic zero
cochain compares the two cocycles by a literal coboundary.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.NestedPeriodCocycle

open PeriodFamilyHigherDirectImage HolomorphicFunctionSheaf.SphereH1

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  {U W : Opens B}

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The actual larger-family primitive evaluated on the two original lifts. -/
def difference (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) (k : (W × ComplexPlane₂) × (U × ComplexPlane₂))
    (x : (Restriction.restrictedPeriods P U).TotalSpace) : ℂ :=
  Cocycle.primitive (Restriction.restrictedPeriods P W) a (originalLift P h k x) -
    Cocycle.primitive (Restriction.restrictedPeriods P W) a (nativeLift P h k x)

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The literal change of primitive is holomorphic in the original smaller-family atlas. -/
theorem difference_holomorphicAt (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) (k : (W × ComplexPlane₂) × (U × ComplexPlane₂))
    {x : (Restriction.restrictedPeriods P U).TotalSpace}
    (hx : x ∈ commonCover P h k) :
    letI := (Restriction.restrictedPeriods P U).totalChartedSpace
    ContMDiffAt IT 𝓘(ℂ) ω (difference P h a k) x := by
  let := (Restriction.restrictedPeriods P U).totalChartedSpace
  let := (Restriction.restrictedPeriods P W).totalChartedSpace
  exact PrimitiveDifference.difference_holomorphicAt
    (Restriction.restrictedPeriods P W) a (familyMap P h)
    (originalLift P h k) (nativeLift P h k)
    (originalLift_continuousAt P h k hx) (nativeLift_continuousAt P h k hx)
    (originalLift_project_eventuallyEq P h k hx)
    (nativeLift_project_eventuallyEq P h k hx)
    (familyMap_holomorphic P h).contMDiffAt

/-- The genuine native holomorphic section supplied by the change of primitive. -/
def differenceSection (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) (k : (W × ComplexPlane₂) × (U × ComplexPlane₂)) :
    Cocycle.NativeSection (Restriction.restrictedPeriods P U) (commonCover P h k) := by
  letI := (Restriction.restrictedPeriods P U).totalChartedSpace
  refine ⟨fun x => difference P h a k x, ?_⟩
  intro x
  exact (difference_holomorphicAt P h a k x.property).comp x (contMDiff_subtype_val x)

/-- Values use the original primitive and its literal coefficient restriction. -/
theorem differenceSection_apply (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) (k : (W × ComplexPlane₂) × (U × ComplexPlane₂))
    (x : commonCover P h k) :
    differenceSection P h a k x =
      Cocycle.primitive (Restriction.restrictedPeriods P W) a
        (Cocycle.lift (Restriction.restrictedPeriods P W) k.1 (familyMap P h x)) -
      Cocycle.primitive (Restriction.restrictedPeriods P U) (restrictedCoefficients h a)
        (Cocycle.lift (Restriction.restrictedPeriods P U) k.2 x) := rfl

/-- The literal pullback cocycle refined to the actual intersection cover. -/
def commonPullbackCocycle (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) :
    CechOneCocycle (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P U))
      (commonCover P h) :=
  HolomorphicPicard.Cech.refinement _ Prod.fst (fun _ => inf_le_left)
    (pullbackCocycle P h a)

/-- The independently constructed smaller-family cocycle on the same refinement. -/
def commonNativeCocycle (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) :
    CechOneCocycle (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P U))
      (commonCover P h) :=
  HolomorphicPicard.Cech.refinement _ Prod.snd (fun _ => inf_le_right)
    (Cocycle.cocycle (Restriction.restrictedPeriods P U) (restrictedCoefficients h a))

/-- The actual holomorphic zero cochain, with the original first-minus-second sign. -/
def comparisonCochain (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) :
    HolomorphicPicard.Cech.ZeroCochain
      (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P U)) (commonCover P h) :=
  differenceSection P h a

/-- The difference of the two actual refined cocycles is this genuine coboundary. -/
theorem commonCocycle_sub_eq_coboundary (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) :
    commonPullbackCocycle P h a - commonNativeCocycle P h a =
      HolomorphicPicard.Cech.coboundary
        (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P U))
        (commonCover P h) (comparisonCochain P h a) := by
  let := (Restriction.restrictedPeriods P U).totalChartedSpace
  apply HolomorphicPicard.Cech.cocycle_ext
  intro k l
  apply ContMDiffMap.ext
  intro x
  change (Cocycle.primitive (Restriction.restrictedPeriods P W) a (originalLift P h k x) -
      Cocycle.primitive (Restriction.restrictedPeriods P W) a (originalLift P h l x)) -
    (Cocycle.primitive (Restriction.restrictedPeriods P W) a (nativeLift P h k x) -
      Cocycle.primitive (Restriction.restrictedPeriods P W) a (nativeLift P h l x)) =
    (Cocycle.primitive (Restriction.restrictedPeriods P W) a (originalLift P h k x) -
      Cocycle.primitive (Restriction.restrictedPeriods P W) a (nativeLift P h k x)) -
    (Cocycle.primitive (Restriction.restrictedPeriods P W) a (originalLift P h l x) -
      Cocycle.primitive (Restriction.restrictedPeriods P W) a (nativeLift P h l x))
  abel

end OpenClassRestriction.NestedPeriodCocycle
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
