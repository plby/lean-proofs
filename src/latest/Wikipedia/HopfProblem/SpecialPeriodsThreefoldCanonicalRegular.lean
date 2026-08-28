import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPatches
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularGeometry
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalRegular

/-!
# The native regular canonical bundle inside the actual threefold

The canonical bundle compared here is literally the already constructed
canonical bundle of the special regular triangle quotient.  Its native
atlas is unchanged.  Comparison with the global canonical bundle is
pullback by the derivative of the actual full regular-patch inclusion.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Regular

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace specialRegularFamilyChartedSpace

local instance regularGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

local instance regularNativeManifold : IsManifold IF ω Threefold.SpecialRegularFamily :=
  specialRegularFamily_isManifold

/-- The original regular quotient, with no new complex structure. -/
abbrev LocalSpace := Threefold.SpecialRegularFamily

theorem native_chartedSpace_eq :
    specialRegularFamilyChartedSpace =
      TrianglePeriodFamily.Canonical.specialRegularCanonicalChartedSpace := rfl

/-- Literally the earlier regular-family canonical bundle. -/
abbrev bundle := TrianglePeriodFamily.Canonical.specialRegularCanonicalBundle

theorem bundle_eq_piece : bundle = Threefold.Canonical.localBundle none := rfl

def intrinsicEquiv (x : LocalSpace) :
    bundle.Fiber x ≃L[ℂ] (TangentSpace IF x) [⋀^(Fin 3)]→L[ℂ] ℂ :=
  TrianglePeriodFamily.Canonical.specialRegularCanonicalIntrinsicEquiv x

/-- The actual full-patch comparison with the old regular canonical bundle. -/
def pullbackEquiv (x : LocalSpace) :
    Threefold.Canonical.bundle.Fiber (regularFamilyInclusion x) ≃L[ℂ] bundle.Fiber x :=
  Pullback.pullbackEquiv regularFamilyInclusion_isLocalDiffeomorph x

theorem pullback_intrinsic (x : LocalSpace)
    (v : Threefold.Canonical.bundle.Fiber (regularFamilyInclusion x)) :
    intrinsicEquiv x (pullbackEquiv x v) =
      (Threefold.Canonical.intrinsicEquiv (regularFamilyInclusion x) v).compContinuousLinearMap
        (mfderiv IF IF regularFamilyInclusion x) :=
  Pullback.intrinsic_pullbackEquiv regularFamilyInclusion_isLocalDiffeomorph x v

theorem pullback_preferred_coefficient (x : LocalSpace)
    (v : Threefold.Canonical.bundle.Fiber (regularFamilyInclusion x)) :
    id (α := ℂ) (pullbackEquiv x v) =
      LinearMap.det (mfderiv IF IF regularFamilyInclusion x).toLinearMap * id (α := ℂ) v :=
  Pullback.pullbackLinear_preferred_coefficient regularFamilyInclusion x v

/-- The inverse comparison over the full actual regular inclusion. -/
def pushforward : bundle.TotalSpace → Threefold.Canonical.bundle.TotalSpace :=
  Threefold.Canonical.patchPushforward none

@[simp] theorem pushforward_proj (p : bundle.TotalSpace) :
    (pushforward p).proj = regularFamilyInclusion p.proj := rfl

theorem pushforward_intrinsic (x : LocalSpace) (v : bundle.Fiber x) :
    Threefold.Canonical.intrinsicEquiv (regularFamilyInclusion x)
      (pushforward ⟨x, v⟩).2 =
        (intrinsicEquiv x v).compContinuousLinearMap
          ((regularFamilyInclusion_isLocalDiffeomorph x).mfderivToContinuousLinearEquiv
            (by simp)).symm.toContinuousLinearMap :=
  Pullback.intrinsic_pullbackEquivAt_symm (regularFamilyInclusion_isLocalDiffeomorph x) v

theorem pushforward_injective : Function.Injective pushforward :=
  Threefold.Canonical.patchPushforward_injective none

theorem pushforward_range : range pushforward =
    (Bundle.TotalSpace.proj : Threefold.Canonical.bundle.TotalSpace → Threefold.Space) ⁻¹'
      (regularLocus : Set Threefold.Space) :=
  Threefold.Canonical.patchPushforward_range none

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Regular
