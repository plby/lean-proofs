import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspGeometry
import Wikipedia.HopfProblem.CuspCanonicalBundle

/-!
# Intrinsic covectors of the actual native cusp canonical bundle

The cusp canonical bundle constructed from the toric volume charts is
identified with the full space of alternating three-covectors on the
native tangent space.  The identification uses the actual preferred
chart, and the descended toric form retains its signed volume coefficient.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp

open ToricCharts CuspGeometry

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] CuspGeometry.nativeChartedSpace

local instance nativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold

/-- Its actual toric-volume atlas, with the native quotient charts. -/
abbrev nativeVolumeAtlas : CanonicalBundle.ConstantVolumeAtlas LocalSpace LocalSpace :=
  CuspQuotient.volumeAtlas data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift

/-- The original inverse-Jacobian bundle of the actual restricted cusp quotient. -/
abbrev nativeBundle : VectorBundleCore ℂ LocalSpace ℂ LocalSpace := nativeVolumeAtlas.core

/-- The signed determinant of the toric chart used in the preferred quotient lift. -/
abbrev nativeVolumeCoefficient (x : LocalSpace) : ℂ :=
  CuspQuotient.volumeCoefficient data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift x

theorem nativeVolumeCoefficient_ne_zero (x : LocalSpace) : nativeVolumeCoefficient x ≠ 0 :=
  CuspQuotient.volumeCoefficient_ne_zero data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift x

/-- Full continuous alternating three-covectors on the actual native tangent space. -/
abbrev NativeIntrinsicTopCovector (x : LocalSpace) :=
  (TangentSpace I₃ x) [⋀^(Fin 3)]→L[ℂ] ℂ

/-- Intrinsic identification through the preferred native tangent chart. -/
def nativeIntrinsicEquiv (x : LocalSpace) :
    nativeBundle.Fiber x ≃L[ℂ] NativeIntrinsicTopCovector x :=
  nativeVolumeAtlas.coordinateEquiv x (mem_chart_source (CoordinateSpace 3) x)

@[simp] theorem nativeIntrinsicEquiv_apply (x : LocalSpace) (v : nativeBundle.Fiber x) :
    nativeIntrinsicEquiv x v = nativeVolumeAtlas.inCoordinates x x v := rfl

/-- In any native chart, the same intrinsic covector is represented by
pullback through the genuine change from that chart to the tangent chart. -/
theorem native_inCoordinates_eq_intrinsic_pullback (i : LocalSpace) {x : LocalSpace}
    (hi : x ∈ (chartAt (CoordinateSpace 3) i).source) (v : nativeBundle.Fiber x) :
    nativeVolumeAtlas.inCoordinates i x v =
      (nativeIntrinsicEquiv x v).compContinuousLinearMap
        (fderiv ℂ ((chartAt (CoordinateSpace 3) i).symm.trans
          (chartAt (CoordinateSpace 3) x)) (chartAt (CoordinateSpace 3) i x)) :=
  nativeVolumeAtlas.inCoordinates_change x i
    (mem_chart_source (CoordinateSpace 3) x) hi v

/-- The original descended toric volume form, in the original cusp bundle. -/
abbrev nativeVolume (x : LocalSpace) : nativeBundle.Fiber x :=
  CuspQuotient.canonicalVolume data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift x

theorem nativeVolume_ne_zero (x : LocalSpace) : nativeVolume x ≠ 0 :=
  CuspQuotient.canonicalVolume_ne_zero data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift x

theorem nativeVolume_holomorphic :
    ContMDiff I₃ ((I₃).prod I₁) ω
      (fun x => (⟨x, nativeVolume x⟩ : nativeBundle.TotalSpace)) :=
  CuspQuotient.canonicalVolume_holomorphic data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift

/-- The native tangent form keeps the exact signed toric determinant. -/
theorem nativeIntrinsicEquiv_volume (x : LocalSpace) :
    nativeIntrinsicEquiv x (nativeVolume x) =
      nativeVolumeCoefficient x • CanonicalBundle.volume :=
  CuspQuotient.canonicalVolume_in_coordinates data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift x x

theorem nativeIntrinsicVolume_ne_zero (x : LocalSpace) :
    nativeIntrinsicEquiv x (nativeVolume x) ≠ 0 := by
  intro h
  apply nativeVolume_ne_zero x
  exact (nativeIntrinsicEquiv x).injective (h.trans (map_zero _).symm)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp
