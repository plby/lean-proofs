import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspPullbackLog

/-!
# Genuine canonical-fibre comparison on the logarithmic cusp cover

The original exponential and the actual toric quotient are local
biholomorphisms. Their composite with the actual global inclusion thus
identifies the full canonical fibre with the top alternating covectors on
the original logarithmic tangent space. In particular this pullback is
injective; it is not a compatibility hypothesis on sections.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback

open ToricCharts CuspUniformization CuspGeometry HolomorphicForms.Cusp

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance comparisonNativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance comparisonGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- The original covering quotient is locally biholomorphic in its native atlas. -/
theorem nativeQuotientMap_isLocalDiffeomorph : IsLocalDiffeomorph I₃ I₃ ω nativeQuotientMap :=
  CuspUniformization.quotientMap_isLocalDiffeomorph data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift

/-- The literal native logarithmic cusp uniformization is locally biholomorphic. -/
theorem localLogMap_isLocalDiffeomorph : IsLocalDiffeomorph IF I₃ ω localLogMap := by
  intro x
  change IsLocalDiffeomorphAt IF I₃ ω
    (nativeQuotientMap ∘ totalExponentialLift data.radius) x
  exact (totalExponentialLift_isLocalDiffeomorph data.radius x).comp
    (K := I₃) (P := LocalSpace)
    (nativeQuotientMap_isLocalDiffeomorph (totalExponentialLift data.radius x))

/-- The original logarithmic cover maps locally biholomorphically to the glued threefold. -/
theorem globalLogMap_isLocalDiffeomorph : IsLocalDiffeomorph IF IF ω globalLogMap := by
  intro x
  change IsLocalDiffeomorphAt IF IF ω (CuspGeometry.inclusion ∘ localLogMap) x
  exact (localLogMap_isLocalDiffeomorph x).comp
    (K := IF) (P := Threefold.Space) (CuspGeometry.inclusion_isLocalDiffeomorph (localLogMap x))

/-- The genuine invertible derivative, retaining the original logarithmic and global tangents. -/
def logarithmicDerivativeEquiv (x : LogDomain) :
    TangentSpace IF x ≃L[ℂ] TangentSpace IF (globalLogMap x) :=
  (globalLogMap_isLocalDiffeomorph x).mfderivToContinuousLinearEquiv (by simp)

@[simp] theorem logarithmicDerivativeEquiv_coe (x : LogDomain) :
    (logarithmicDerivativeEquiv x).toContinuousLinearMap = mfderiv IF IF globalLogMap x := rfl

/-- Actual derivative pullback of all alternating three-covectors is an equivalence. -/
def logarithmicTopCovectorPullback (x : LogDomain) :
    IntrinsicTopCovector (globalLogMap x) ≃L[ℂ] TrianglePeriodFamily.Canonical.TopCovector :=
  (logarithmicDerivativeEquiv x).symm.continuousAlternatingMapCongrLeft

@[simp] theorem logarithmicTopCovectorPullback_apply (x : LogDomain)
    (α : IntrinsicTopCovector (globalLogMap x)) :
    logarithmicTopCovectorPullback x α =
      α.compContinuousLinearMap (mfderiv IF IF globalLogMap x) := rfl

/-- The actual global canonical line, identified through its intrinsic alternating covector. -/
def canonicalLogarithmicPullback (x : LogDomain) :
    bundle.Fiber (globalLogMap x) ≃L[ℂ] TrianglePeriodFamily.Canonical.TopCovector :=
  (intrinsicEquiv (globalLogMap x)).trans (logarithmicTopCovectorPullback x)

@[simp] theorem canonicalLogarithmicPullback_apply (x : LogDomain)
    (v : bundle.Fiber (globalLogMap x)) :
    canonicalLogarithmicPullback x v =
      (intrinsicEquiv (globalLogMap x) v).compContinuousLinearMap
        (mfderiv IF IF globalLogMap x) := rfl

/-- The canonical-fibre equivalence sends the real cusp section to its computed nonzero factor. -/
theorem canonicalLogarithmicPullback_cuspVolume (x : LogDomain) :
    canonicalLogarithmicPullback x (Cusp.volumeAlongInclusion (localLogMap x)) =
      logarithmicVolumeFactor x • TrianglePeriodFamily.Canonical.volume :=
  globalVolume_logarithmic_pullback x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback
