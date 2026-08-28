import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersSquarePrescribed

/-!
# Powers retain the actual sphere ideal-line pullback

The powers of the threefold's negative line are literally the genuine
pullbacks of the corresponding powers of the sphere ideal line.  Their
original native total-space maps are holomorphic, preserve the actual
projection, and agree with the true pulled-back local trivializations.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Powers

open TrianglePeriodFamily.Canonical CanonicalGlobalLineBundle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

/-- This is equality of the actual cocycle data, including the original
inverse-image cover; it is not merely equality of degree labels. -/
theorem basePower_eq_pullback (n : ℕ) :
    baseData.power n = pullback (CanonicalGlobal.BaseTwist.data.power n)
      Threefold.projectionSphere Threefold.projectionSphere_holomorphic.continuous := rfl

/-- The actual fibre is the original sphere power fibre over its image. -/
def basePowerFiberEquiv (n : ℕ) (x : Threefold.Space) :
    (baseData.power n).core.Fiber x ≃L[ℂ]
      (CanonicalGlobal.BaseTwist.data.power n).core.Fiber (Threefold.projectionSphere x) :=
  pullbackFiberEquiv (CanonicalGlobal.BaseTwist.data.power n) Threefold.projectionSphere
    Threefold.projectionSphere_holomorphic.continuous x

def basePowerProjection (n : ℕ) : (baseData.power n).core.TotalSpace →
    (CanonicalGlobal.BaseTwist.data.power n).core.TotalSpace :=
  pullbackTotalMap (CanonicalGlobal.BaseTwist.data.power n) Threefold.projectionSphere
    Threefold.projectionSphere_holomorphic.continuous

theorem basePowerProjection_holomorphic (n : ℕ) :
    ContMDiff Iκ ((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ℂ)) ω
      (basePowerProjection n) :=
  pullbackTotalMap_holomorphic (CanonicalGlobal.BaseTwist.data.power n)
    Threefold.projectionSphere Threefold.projectionSphere_holomorphic.continuous
    IF (modelWithCornersSelf ℂ ℂ) Threefold.projectionSphere_holomorphic

@[simp] theorem basePowerProjection_proj (n : ℕ) (p : (baseData.power n).core.TotalSpace) :
    (basePowerProjection n p).proj = Threefold.projectionSphere p.proj := rfl

theorem basePowerProjection_localTriv (n : ℕ) (i : Bool)
    (p : (baseData.power n).core.TotalSpace) :
    (CanonicalGlobal.BaseTwist.data.power n).core.localTriv i (basePowerProjection n p) =
      (Threefold.projectionSphere p.proj, ((baseData.power n).core.localTriv i p).2) := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Powers
