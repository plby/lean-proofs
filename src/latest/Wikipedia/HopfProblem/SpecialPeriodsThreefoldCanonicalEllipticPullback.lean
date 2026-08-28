import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalElliptic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticParametrization

/-!
# The global canonical bundle on the actual elliptic patches

The canonical fibre comparison is the pullback of genuine ambient
three-covectors along the actual derivative of the native elliptic patch
inclusion.  We also give the comparison on the full filling, precisely on
the source of its actual partial biholomorphism into the global threefold.
In particular, this source contains the entire original central surface.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  Threefold.chartedSpace

local instance fullPullbackManifold (j : Kind) :
    IsManifold IF ω (SpecialFullFilling j) := (specialFullFilling_construction j).2.2.1

local instance piecePullbackManifold (j : Kind) :
    IsManifold IF ω (SpecialEllipticPiece j) := specialEllipticPiece_isManifold j

local instance globalPullbackManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- Pull the actual global canonical fibre back to the native small
elliptic filling using the derivative of its proved patch inclusion. -/
def patchPullback (j : Kind) (x : SpecialEllipticPiece j) :
    Threefold.Canonical.bundle.Fiber (EllipticGeometry.inclusion j x) ≃L[ℂ]
      (bundle j).Fiber x :=
  Pullback.pullbackEquiv (EllipticGeometry.inclusion_isLocalDiffeomorph j) x

@[simp] theorem patchPullback_apply (j : Kind) (x : SpecialEllipticPiece j)
    (v : Threefold.Canonical.bundle.Fiber (EllipticGeometry.inclusion j x)) :
    patchPullback j x v = Pullback.pullbackLinear (EllipticGeometry.inclusion j) x v := rfl

/-- Exact equality on the full ambient alternating covectors. -/
theorem intrinsic_patchPullback (j : Kind) (x : SpecialEllipticPiece j)
    (v : Threefold.Canonical.bundle.Fiber (EllipticGeometry.inclusion j x)) :
    intrinsicEquiv j x (patchPullback j x v) =
      (Threefold.Canonical.intrinsicEquiv
        (EllipticGeometry.inclusion j x) v).compContinuousLinearMap
          (mfderiv IF IF (EllipticGeometry.inclusion j) x) :=
  Pullback.intrinsic_pullbackEquiv (EllipticGeometry.inclusion_isLocalDiffeomorph j) x v

/-- The inverse comparison is pullback along the inverse of the actual
derivative; no unrelated fibre identification is substituted. -/
theorem intrinsic_patchPullback_symm (j : Kind) (x : SpecialEllipticPiece j)
    (v : (bundle j).Fiber x) :
    Threefold.Canonical.intrinsicEquiv (EllipticGeometry.inclusion j x)
        ((patchPullback j x).symm v) =
      (intrinsicEquiv j x v).compContinuousLinearMap
        ((EllipticGeometry.inclusion_isLocalDiffeomorph j x).mfderivToContinuousLinearEquiv
          (by simp)).symm.toContinuousLinearMap :=
  Pullback.intrinsic_pullbackEquivAt_symm (EllipticGeometry.inclusion_isLocalDiffeomorph j x) v

/-- The native preferred-coordinate coefficient is the determinant of
the actual manifold derivative of the patch inclusion. -/
theorem patchPullback_preferred_coefficient (j : Kind) (x : SpecialEllipticPiece j)
    (v : Threefold.Canonical.bundle.Fiber (EllipticGeometry.inclusion j x)) :
    id (α := ℂ) (patchPullback j x v) =
      LinearMap.det (mfderiv IF IF (EllipticGeometry.inclusion j) x).toLinearMap *
        id (α := ℂ) v :=
  Pullback.pullbackLinear_preferred_coefficient (EllipticGeometry.inclusion j) x v

/-- Pullback to the original full elliptic filling on its exact actual
parametrization source. -/
def fullPatchPullback (j : Kind) (x : SpecialFullFilling j)
    (hx : x ∈ (EllipticGeometry.fullParametrization j).source) :
    Threefold.Canonical.bundle.Fiber (EllipticGeometry.fullParametrization j x) ≃L[ℂ]
      (fullBundle j).Fiber x :=
  Pullback.pullbackEquivAt (EllipticGeometry.fullParametrization_isLocalDiffeomorphAt j hx)

@[simp] theorem fullPatchPullback_apply (j : Kind) (x : SpecialFullFilling j)
    (hx : x ∈ (EllipticGeometry.fullParametrization j).source)
    (v : Threefold.Canonical.bundle.Fiber (EllipticGeometry.fullParametrization j x)) :
    fullPatchPullback j x hx v =
      Pullback.pullbackLinear (EllipticGeometry.fullParametrization j) x v := rfl

theorem intrinsic_fullPatchPullback (j : Kind) (x : SpecialFullFilling j)
    (hx : x ∈ (EllipticGeometry.fullParametrization j).source)
    (v : Threefold.Canonical.bundle.Fiber (EllipticGeometry.fullParametrization j x)) :
    fullIntrinsicEquiv j x (fullPatchPullback j x hx v) =
      (Threefold.Canonical.intrinsicEquiv
        (EllipticGeometry.fullParametrization j x) v).compContinuousLinearMap
          (mfderiv IF IF (EllipticGeometry.fullParametrization j) x) :=
  Pullback.intrinsic_pullbackEquivAt
    (EllipticGeometry.fullParametrization_isLocalDiffeomorphAt j hx) v

theorem intrinsic_fullPatchPullback_symm (j : Kind) (x : SpecialFullFilling j)
    (hx : x ∈ (EllipticGeometry.fullParametrization j).source)
    (v : (fullBundle j).Fiber x) :
    Threefold.Canonical.intrinsicEquiv (EllipticGeometry.fullParametrization j x)
        ((fullPatchPullback j x hx).symm v) =
      (fullIntrinsicEquiv j x v).compContinuousLinearMap
        (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
          (EllipticGeometry.fullParametrization_isLocalDiffeomorphAt j hx)
          (by simp)).symm.toContinuousLinearMap :=
  Pullback.intrinsic_pullbackEquivAt_symm
    (EllipticGeometry.fullParametrization_isLocalDiffeomorphAt j hx) v

theorem fullPatchPullback_preferred_coefficient (j : Kind) (x : SpecialFullFilling j)
    (hx : x ∈ (EllipticGeometry.fullParametrization j).source)
    (v : Threefold.Canonical.bundle.Fiber (EllipticGeometry.fullParametrization j x)) :
    id (α := ℂ) (fullPatchPullback j x hx v) =
      LinearMap.det (mfderiv IF IF (EllipticGeometry.fullParametrization j) x).toLinearMap *
        id (α := ℂ) v :=
  Pullback.pullbackLinear_preferred_coefficient (EllipticGeometry.fullParametrization j) x v

/-- Every point of the central surface has the ambient threefold
canonical comparison, with domain membership proved from the actual filling. -/
def centralAmbientPullback (j : Kind) (x : SpecialCentralSurface j) :
    Threefold.Canonical.bundle.Fiber
        (EllipticGeometry.fullParametrization j (specialCentralInclusion j x)) ≃L[ℂ]
      (fullBundle j).Fiber (specialCentralInclusion j x) :=
  fullPatchPullback j (specialCentralInclusion j x)
    (EllipticGeometry.specialCentralInclusion_mem_fullParametrization_source j x)

theorem intrinsic_centralAmbientPullback (j : Kind) (x : SpecialCentralSurface j)
    (v : Threefold.Canonical.bundle.Fiber
      (EllipticGeometry.fullParametrization j (specialCentralInclusion j x))) :
    fullIntrinsicEquiv j (specialCentralInclusion j x) (centralAmbientPullback j x v) =
      ContinuousAlternatingMap.compContinuousLinearMap
        (Threefold.Canonical.intrinsicEquiv
          (EllipticGeometry.fullParametrization j (specialCentralInclusion j x)) v)
        (mfderiv IF IF (EllipticGeometry.fullParametrization j) (specialCentralInclusion j x)) :=
  intrinsic_fullPatchPullback j (specialCentralInclusion j x)
    (EllipticGeometry.specialCentralInclusion_mem_fullParametrization_source j x) v

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic
