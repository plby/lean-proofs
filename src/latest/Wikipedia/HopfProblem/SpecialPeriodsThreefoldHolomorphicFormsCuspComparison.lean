import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspComparisonBase

/-!
# The exact global comparison of cusp and regular logarithmic covers

The constructed sphere-normalized periods agree on the logarithmic cusp base.
The original punctured cusp biholomorphism, the actual cyclic-family quotient,
and the actual vector-cover period comparison therefore identify the two maps
on every logarithmic covering point. The final equality takes place in the
actual glued threefold, by its proved gluing relation.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open CuspFamily CuspUniformization Triangle

local notation "C" => CuspGeometry.data
local notation "D" => RegularCover.data

attribute [local instance] triangleCompactifiedChartedSpace
  CuspGeometry.nativeChartedSpace specialRegularFamilyChartedSpace Threefold.chartedSpace

/-- The constructed regular and cusp periods agree at every actual logarithmic base point. -/
theorem logarithmic_period_agreement (s : LogBase (C).radius) :
    (D).periods.point (logBaseToRegular (C).radius radius_cap s) = (C).periods.point s :=
  CuspGlobalOverlap.spherePeriod_agreement triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo (specialBaseCover.radius none)
    (specialBaseCover.radius_pos none) specialCuspRadius_le radius_cap s

/-- The image of every logarithmic point lies in the full native cusp-overlap source. -/
theorem localLogMap_mem_nativeOverlap (x : LogDomain) :
    localLogMap x ∈ specialCuspNativeOverlap.source := by
  apply (specialCuspNativeOverlap_source_iff (localLogMap x)).mpr
  change CuspQuotient.projection (C).correction (C).radius
    (totalCuspCover (C).correction (C).radius x) ≠ 0
  rw [projection_totalCuspCover]
  exact exponential_ne_zero _

/-- The identical source statement in the common atlas used by the global gluing. -/
theorem localLogMap_mem_overlap (x : LogDomain) :
    localLogMap x ∈ specialCuspOverlap.source := by
  change localLogMap x ∈ (univ : Set SpecialCuspPiece) ∧
    localLogMap x ∈ specialCuspNativeOverlap.source
  exact ⟨mem_univ _, localLogMap_mem_nativeOverlap x⟩

/-- The real-coordinate family quotient and the genuine vector quotient give the same point. -/
theorem familyMap_iteratedCover_eq_regular (x : LogDomain) :
    CuspGlobalOverlap.familyMap C D radius_cap ((C).iteratedCover x) =
      (D).quotient ((D).periods.quotientMap (toRegularCover x)) := by
  change CuspGlobalOverlap.familyMap C D radius_cap ((C).quotient ((C).familyCover x)) = _
  rw [CuspGlobalOverlap.familyMap_quotient]
  apply congrArg (D).quotient
  change HolomorphicPeriodMap.periodPullbackMap (C).periods (D).periods
      (logBaseToRegular (C).radius radius_cap)
      ((C).periods.quotientMap (logCoverProductEquiv (C).radius x)) =
    (D).periods.quotientMap (HolomorphicPeriodMap.periodPullbackVectorMap
      (logBaseToRegular (C).radius radius_cap) (logCoverProductEquiv (C).radius x))
  exact HolomorphicPeriodMap.periodPullbackMap_quotientMap (C).periods (D).periods
    (logBaseToRegular (C).radius radius_cap) logarithmic_period_agreement _

/-- On the entire logarithmic cover the actual native overlap is the regular vector quotient. -/
theorem nativeOverlap_localLogMap (x : LogDomain) :
    specialCuspNativeOverlap (localLogMap x) =
      (D).quotient ((D).periods.quotientMap (toRegularCover x)) := by
  let := CuspQuotient.chartedSpace (C).correction (C).radius (C).radius_pos (C).radius_lt_one
    (C).holomorphic (C).smallDrift
  let := (D).chartedSpace (CuspGlobalOverlap.familyCovering D)
  have hx : localLogMap x ∈ puncturedQuotientOpen (C).correction (C).radius := by
    change CuspQuotient.projection (C).correction (C).radius
      (totalCuspCover (C).correction (C).radius x) ≠ 0
    rw [projection_totalCuspCover]
    exact exponential_ne_zero _
  change CuspGlobalOverlap.cuspToRegularPartial C D radius_cap logarithmic_period_agreement
    (localLogMap x) = _
  rw [CuspGlobalOverlap.cuspToRegularPartial_apply C D radius_cap
    logarithmic_period_agreement (localLogMap x) hx]
  change (CuspGlobalOverlap.puncturedBiholomorph C D radius_cap logarithmic_period_agreement
    (puncturedCuspCover (C).correction (C).radius x) : (D).Space) = _
  rw [CuspGlobalOverlap.puncturedBiholomorph_cover]
  exact familyMap_iteratedCover_eq_regular x

/-- The complete cusp logarithmic cover and regular cover have exactly the same global image map. -/
theorem globalLogMap_eq_regularCover (x : LogDomain) :
    globalLogMap x = RegularCover.globalCover (toRegularCover x) := by
  have he : globalLogMap x =
      regularFamilyInclusion (specialCuspOverlap (localLogMap x)) := by
    change gluingData.inclusion (some none) _ = gluingData.inclusion none _
    exact (gluingData.inclusion_eq_iff (some none) none _ _).mpr
      ⟨localLogMap_mem_overlap x, rfl⟩
  rw [specialCuspOverlap_apply, nativeOverlap_localLogMap] at he
  exact he

/-- Equality of the actual maps, suitable for derivative and genuine pullback functoriality. -/
theorem globalLogMap_eq_regularCover_comp :
    globalLogMap = RegularCover.globalCover ∘ toRegularCover :=
  funext globalLogMap_eq_regularCover

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
