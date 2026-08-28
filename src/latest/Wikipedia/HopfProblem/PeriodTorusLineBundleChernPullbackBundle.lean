import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackBundleGauge
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackBundleNative

/-!
# The actual factor bundle is the native line-bundle pullback

The cross-cover factor comparison and the native pullback identification
give an analytic fibrewise complex-linear isomorphism with Mathlib's
actual pullback bundle.  Its map to the target native total space sends
the genuine representative `[z,c]` to `[L z,c]`.  No pullback relation,
bundle isomorphism, or characteristic-class formula is assumed.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

variable {p q : PeriodDomain} (L : LatticeLinearMap p q) (F : FactorOfAutomorphy q)

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The actual analytic, complex-fibre-linear identification with the native pullback bundle. -/
def pullbackBundleIso : AnalyticBundleIso IC (Core.data (pullbackFactor L F)).core.Fiber
    ((L.torusMap : p.Torus → q.Torus) *ᵖ (Core.data F).core.Fiber) :=
  (pullbackCoreIso L F).trans (pullbackNativeIso (Core.data F) IC IC L.torusMap)

/-- The native pullback lift agrees with the independently descended factor-quotient map. -/
theorem pullbackBundleIso_lift (u : (Core.data (pullbackFactor L F)).core.TotalSpace) :
    Bundle.Pullback.lift (L.torusMap : p.Torus → q.Torus)
        ((pullbackBundleIso L F).diffeomorph u) =
      Core.fromAssociated F
        (pullbackAssociatedMap L F (Core.toAssociated (pullbackFactor L F) u)) := by
  change Bundle.Pullback.lift (L.torusMap : p.Torus → q.Torus)
      ((pullbackNativeIso (Core.data F) IC IC L.torusMap).diffeomorph
        ((pullbackCoreIso L F).diffeomorph u)) = _
  rw [pullbackNativeIso_lift, pullbackCoreIso_totalMap]

/-- On actual covering representatives the native total-space diagram
is exactly `(z,c) ↦ (Lz,c)`. -/
theorem pullbackBundleIso_lift_fromAssociated (z : ComplexPlane₂) (c : ℂ) :
    Bundle.Pullback.lift (L.torusMap : p.Torus → q.Torus)
        ((pullbackBundleIso L F).diffeomorph
          (Core.fromAssociated (pullbackFactor L F)
            (associatedMap (pullbackFactor L F) (z, c)))) =
      Core.fromAssociated F (associatedMap F (L.linear z, c)) := by
  rw [pullbackBundleIso_lift, Core.toAssociated_fromAssociated,
    pullbackAssociatedMap_associatedMap]

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback
