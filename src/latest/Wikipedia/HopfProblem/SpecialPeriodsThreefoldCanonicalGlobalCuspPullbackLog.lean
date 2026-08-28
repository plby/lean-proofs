import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspPullbackReference
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspPullbackExponential
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspLogCover

/-!
# Pullback of the cusp canonical volume through the actual logarithmic cover

The original logarithmic uniformization factors through the reference toric
chart by its literal exponential coordinates.  The genuine derivative chain
rule therefore gives the precise factor `(2πi)^3 q` in the native and global
canonical bundles, without an assumed compatibility of local forms.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback

open ToricCharts CuspUniformization CuspGeometry HolomorphicForms.Cusp

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance logNativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance logGlobalManifold : IsManifold IF ω Threefold.Space := Threefold.space_isManifold

/-- The literal exponential coordinates, in the unchanged reference-chart domain. -/
def referenceExponentialLift (x : LogDomain) : referenceDomain :=
  ⟨refExp x.val, by
    rw [mem_referenceDomain, time_refExp]
    exact (mem_logDomain data.radius x.val).mp x.property⟩

@[simp] theorem referenceExponentialLift_val (x : LogDomain) :
    (referenceExponentialLift x : CoordinateSpace 3) = refExp x.val := rfl

theorem referenceExponentialLift_holomorphic :
    ContMDiff IF I₃ ω referenceExponentialLift := by
  intro x
  have he : ContMDiffAt IF I₃ ω
      (fun y : LogDomain => (referenceExponentialLift y : CoordinateSpace 3)) x ↔
        ContMDiffAt IF I₃ ω referenceExponentialLift x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((refExp_holomorphic.contMDiff.comp contMDiff_subtype_val) x)

/-- The native derivative equals the already computed true exponential derivative. -/
theorem referenceExponentialLift_mfderiv (x : LogDomain) :
    mfderiv IF I₃ referenceExponentialLift x = fderiv ℂ refExp x.val := by
  have hf := referenceExponentialLift_holomorphic.mdifferentiable (by simp) x
  have hs : MDifferentiableAt IF IF (extChartAt IF x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source (ℂ × ComplexPlane₂) x)
  have ht : MDifferentiableAt I₃ I₃
      (extChartAt I₃ (referenceExponentialLift x)) (referenceExponentialLift x) :=
    mdifferentiableAt_extChartAt
      (mem_chart_source (CoordinateSpace 3) (referenceExponentialLift x))
  have he : MDifferentiableAt IF I₃ refExp x.val :=
    refExp_holomorphic.contMDiff.mdifferentiable (by simp) x.val
  have hfun : (extChartAt I₃ (referenceExponentialLift x)) ∘ referenceExponentialLift =
      refExp ∘ extChartAt IF x := rfl
  have hl := mfderiv_comp x ht hf
  have hr := mfderiv_comp x he hs
  have h := hl.symm.trans ((mfderiv_congr (I := IF) (I' := I₃) (x := x) hfun).trans hr)
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : (ℂ × ComplexPlane₂) →L[ℂ] CoordinateSpace 3 => L v) h
  change mfderiv I₃ I₃ (extChartAt I₃ (referenceExponentialLift x))
    (referenceExponentialLift x) (mfderiv IF I₃ referenceExponentialLift x v) =
      mfderiv IF I₃ refExp (extChartAt IF x x) (mfderiv IF IF (extChartAt IF x) x v) at hv
  rw [mfderiv_extChartAt_self, mfderiv_extChartAt_self] at hv
  change mfderiv IF I₃ referenceExponentialLift x v = mfderiv IF I₃ refExp x.val v at hv
  exact hv.trans (congrArg (fun L : (ℂ × ComplexPlane₂) →L[ℂ] CoordinateSpace 3 => L v)
    (mfderiv_eq_fderiv (f := refExp)))

/-- The reference toric lift is literally the original exponential lift. -/
theorem referenceLift_exponential (x : LogDomain) :
    referenceLift (referenceExponentialLift x) = totalExponentialLift data.radius x := by
  apply Subtype.ext
  change ToricSpace.inclusion ToricSpace.referenceTriangle (refExp x.val) =
    ToricSpace.inclusion ToricSpace.referenceTriangle
      (monomial ToricSpace.referenceTriangle.dual (totalExponentialCoordinates x.val))
  rw [monomial_reference_dual_totalExponential]

/-- The factorization is an equality of the actual native cusp maps. -/
theorem localLogMap_eq_reference_comp :
    localLogMap = referenceQuotient ∘ referenceExponentialLift := by
  funext x
  change nativeQuotientMap (totalExponentialLift data.radius x) =
    nativeQuotientMap (referenceLift (referenceExponentialLift x))
  rw [referenceLift_exponential]

/-- Its global version uses the existing cusp inclusion, with no replacement atlas. -/
theorem globalLogMap_eq_reference_comp :
    globalLogMap = referenceMap ∘ referenceExponentialLift := by
  funext x
  exact congrArg CuspGeometry.inclusion
    (congrFun localLogMap_eq_reference_comp x)

/-- The exact nonzero scalar in the original logarithmic coordinates. -/
def logarithmicVolumeFactor (x : LogDomain) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ) ^ 3 * exponential x.val.1

theorem logarithmicVolumeFactor_ne_zero (x : LogDomain) : logarithmicVolumeFactor x ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ exponential_factor_ne_zero) (exponential_ne_zero _)

/-- Genuine alternating-cotangent pullback of the native cusp canonical section. -/
theorem nativeVolume_logarithmic_pullback (x : LogDomain) :
    ContinuousAlternatingMap.compContinuousLinearMap
      (Cusp.nativeIntrinsicEquiv (localLogMap x) (Cusp.nativeVolume (localLogMap x)))
      (mfderiv IF I₃ localLogMap x) =
        logarithmicVolumeFactor x • TrianglePeriodFamily.Canonical.volume := by
  rw [localLogMap_eq_reference_comp, mfderiv_comp x
    (referenceQuotient_holomorphic.mdifferentiable (by simp) (referenceExponentialLift x))
    (referenceExponentialLift_holomorphic.mdifferentiable (by simp) x)]
  change ((Cusp.nativeIntrinsicEquiv (referenceQuotient (referenceExponentialLift x))
    (Cusp.nativeVolume (referenceQuotient (referenceExponentialLift x)))).compContinuousLinearMap
      (mfderiv I₃ I₃ referenceQuotient (referenceExponentialLift x))).compContinuousLinearMap
        (mfderiv IF I₃ referenceExponentialLift x) = _
  rw [nativeVolume_reference_pullback, referenceExponentialLift_mfderiv]
  exact referenceExponential_volume_pullback x.val

/-- The same exact formula for the true canonical section of the glued threefold. -/
theorem globalVolume_logarithmic_pullback (x : LogDomain) :
    (intrinsicEquiv (globalLogMap x)
      (Cusp.volumeAlongInclusion (localLogMap x))).compContinuousLinearMap
        (mfderiv IF IF globalLogMap x) =
          logarithmicVolumeFactor x • TrianglePeriodFamily.Canonical.volume := by
  change (intrinsicEquiv (CuspGeometry.inclusion (localLogMap x))
    (Cusp.volumeAlongInclusion (localLogMap x))).compContinuousLinearMap
      (mfderiv IF IF (CuspGeometry.inclusion ∘ localLogMap) x) = _
  rw [mfderiv_comp x
    (CuspGeometry.inclusion_holomorphic.mdifferentiable (by simp) (localLogMap x))
    (localLogMap_holomorphic.mdifferentiable (by simp) x)]
  change ((intrinsicEquiv (CuspGeometry.inclusion (localLogMap x))
    (Cusp.volumeAlongInclusion (localLogMap x))).compContinuousLinearMap
      (mfderiv I₃ IF CuspGeometry.inclusion (localLogMap x))).compContinuousLinearMap
        (mfderiv IF I₃ localLogMap x) = _
  rw [← Cusp.inclusionPullback_intrinsic, Cusp.inclusionPullback_volumeAlongInclusion]
  exact nativeVolume_logarithmic_pullback x

/-- The full-patch section has that same pullback at every logarithmic covering point. -/
theorem patchVolume_logarithmic_pullback (x : LogDomain) :
    (intrinsicEquiv (globalLogMap x)
      (Cusp.patchVolume (nativePatchBiholomorph (localLogMap x)))).compContinuousLinearMap
        (mfderiv IF IF globalLogMap x) =
          logarithmicVolumeFactor x • TrianglePeriodFamily.Canonical.volume := by
  rw [Cusp.patchVolume_inclusion]
  exact globalVolume_logarithmic_pullback x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback
