import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalBundle
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCuspNative

/-!
# The native cusp form in the actual threefold canonical bundle

The derivative of the actual cusp inclusion identifies the two genuine
canonical fibres, even though the native cusp and the glued threefold
use different coordinate models.  The inverse comparison transports the
original signed toric volume form to the full global cusp patch.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp

open ToricCharts CuspGeometry

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance comparisonNativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance globalManifold : IsManifold IF ω Threefold.Space := Threefold.space_isManifold

/-- The genuine derivative of the native cusp inclusion is a complex-linear
equivalence between its different native and global tangent models. -/
def inclusionDerivativeEquiv (x : LocalSpace) :
    TangentSpace I₃ x ≃L[ℂ] TangentSpace IF (CuspGeometry.inclusion x) :=
  (inclusion_isLocalDiffeomorph x).mfderivToContinuousLinearEquiv (by simp)

@[simp] theorem inclusionDerivativeEquiv_coe (x : LocalSpace) :
    (inclusionDerivativeEquiv x).toContinuousLinearMap =
      mfderiv I₃ IF CuspGeometry.inclusion x := rfl

/-- Actual cotangent pullback, between the global and the original native
canonical bundles, not between substitute scalar line bundles. -/
def inclusionPullback (x : LocalSpace) :
    bundle.Fiber (CuspGeometry.inclusion x) ≃L[ℂ] nativeBundle.Fiber x :=
  ((intrinsicEquiv (CuspGeometry.inclusion x)).trans
    (inclusionDerivativeEquiv x).symm.continuousAlternatingMapCongrLeft).trans
      (nativeIntrinsicEquiv x).symm

/-- The fibre comparison acts by pullback along the actual `mfderiv`. -/
theorem inclusionPullback_intrinsic (x : LocalSpace) (v : bundle.Fiber (CuspGeometry.inclusion x)) :
    nativeIntrinsicEquiv x (inclusionPullback x v) =
      (intrinsicEquiv (CuspGeometry.inclusion x) v).compContinuousLinearMap
        (mfderiv I₃ IF CuspGeometry.inclusion x) := by
  change (nativeIntrinsicEquiv x) ((nativeIntrinsicEquiv x).symm _) = _
  exact (nativeIntrinsicEquiv x).apply_symm_apply _

/-- The inverse fibre comparison is pullback along the inverse of that
same genuine derivative. -/
theorem inclusionPullback_symm_intrinsic (x : LocalSpace) (v : nativeBundle.Fiber x) :
    intrinsicEquiv (CuspGeometry.inclusion x) ((inclusionPullback x).symm v) =
      (nativeIntrinsicEquiv x v).compContinuousLinearMap
        (inclusionDerivativeEquiv x).symm.toContinuousLinearMap := by
  simp only [inclusionPullback, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The original toric volume, now in the actual global canonical fibre. -/
def volumeAlongInclusion (x : LocalSpace) : bundle.Fiber (CuspGeometry.inclusion x) :=
  (inclusionPullback x).symm (nativeVolume x)

@[simp] theorem inclusionPullback_volumeAlongInclusion (x : LocalSpace) :
    inclusionPullback x (volumeAlongInclusion x) = nativeVolume x :=
  (inclusionPullback x).apply_symm_apply _

theorem volumeAlongInclusion_ne_zero (x : LocalSpace) : volumeAlongInclusion x ≠ 0 := by
  intro h
  apply nativeVolume_ne_zero x
  calc
    nativeVolume x = inclusionPullback x (volumeAlongInclusion x) :=
      (inclusionPullback_volumeAlongInclusion x).symm
    _ = 0 := by rw [h, map_zero]

/-- Exact gluing law for the actual tangent form, with the signed toric
coefficient rather than its absolute value. -/
theorem volumeAlongInclusion_pullback (x : LocalSpace) :
    (intrinsicEquiv (CuspGeometry.inclusion x) (volumeAlongInclusion x)).compContinuousLinearMap
        (mfderiv I₃ IF CuspGeometry.inclusion x) =
      nativeVolumeCoefficient x • CanonicalBundle.volume := by
  rw [← inclusionPullback_intrinsic, inclusionPullback_volumeAlongInclusion,
    nativeIntrinsicEquiv_volume]

theorem volumeAlongInclusion_intrinsic (x : LocalSpace) :
    intrinsicEquiv (CuspGeometry.inclusion x) (volumeAlongInclusion x) =
      (nativeVolumeCoefficient x • CanonicalBundle.volume).compContinuousLinearMap
        (inclusionDerivativeEquiv x).symm.toContinuousLinearMap := by
  exact (inclusionPullback_symm_intrinsic x (nativeVolume x)).trans
    (congrArg (fun α : NativeIntrinsicTopCovector x =>
      α.compContinuousLinearMap (inclusionDerivativeEquiv x).symm.toContinuousLinearMap)
        (nativeIntrinsicEquiv_volume x))

/-- The signed pullback condition uniquely determines the global form. -/
theorem volumeAlongInclusion_unique (x : LocalSpace) (v : bundle.Fiber (CuspGeometry.inclusion x))
    (h : (intrinsicEquiv (CuspGeometry.inclusion x) v).compContinuousLinearMap
      (mfderiv I₃ IF CuspGeometry.inclusion x) =
        nativeVolumeCoefficient x • CanonicalBundle.volume) :
    v = volumeAlongInclusion x := by
  apply (inclusionPullback x).injective
  rw [inclusionPullback_volumeAlongInclusion]
  apply (nativeIntrinsicEquiv x).injective
  rw [inclusionPullback_intrinsic, h, nativeIntrinsicEquiv_volume]

/-- The transported volume on every point of the full actual cusp patch. -/
def patchVolume (y : Threefold.liftedPatch (some none)) : bundle.Fiber y.val :=
  volumeAlongInclusion (nativePatchBiholomorph.symm y)

@[simp] theorem patchVolume_inclusion (x : LocalSpace) :
    patchVolume (nativePatchBiholomorph x) = volumeAlongInclusion x := by
  exact congrArg (fun y : LocalSpace => id (α := ℂ) (volumeAlongInclusion y))
    (nativePatchBiholomorph.symm_apply_apply x)

theorem patchVolume_ne_zero (y : Threefold.liftedPatch (some none)) : patchVolume y ≠ 0 :=
  volumeAlongInclusion_ne_zero (nativePatchBiholomorph.symm y)

/-- This is a section of the genuine global canonical bundle over the
entire actual cusp neighborhood. -/
def patchVolumeSection (y : Threefold.liftedPatch (some none)) : bundle.TotalSpace :=
  ⟨y.val, patchVolume y⟩

@[simp] theorem patchVolumeSection_proj (y : Threefold.liftedPatch (some none)) :
    (patchVolumeSection y).proj = y.val := rfl

theorem patchVolume_pullback (x : LocalSpace) :
    (intrinsicEquiv (CuspGeometry.inclusion x)
      (patchVolume (nativePatchBiholomorph x))).compContinuousLinearMap
        (mfderiv I₃ IF CuspGeometry.inclusion x) =
      nativeVolumeCoefficient x • CanonicalBundle.volume := by
  rw [patchVolume_inclusion]
  exact volumeAlongInclusion_pullback x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp
