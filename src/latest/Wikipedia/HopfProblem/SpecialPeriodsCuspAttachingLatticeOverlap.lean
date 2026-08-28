import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingLatticeBasic

/-!
# The full vector formula for the actual cusp attachment

The genuine cusp-to-regular-family overlap preserves every complex fibre
vector on the original logarithmic covering.  The resulting points are
identified by the actual gluing inclusions.  In particular the native
period torus's zero maps to the regular family's marked basepoint.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching

open Triangle CuspFamily CuspUniformization CuspGlobalOverlap ToricCharts

attribute [local instance] triangleCompactifiedChartedSpace triangleRegularQuotientChartedSpace
  specialRegularFamilyChartedSpace specialCuspPieceChartedSpace

/-- The actual cyclic-to-regular-family comparison preserves every vector,
using equality of the genuine period points at the logarithmic base lift. -/
theorem familyMap_iteratedCover_logVector (s : LogBase radius) (z : ComplexPlane₂) :
    familyMap data regularData radius_le_cuspChart (data.iteratedCover (logVector s z)) =
      regularData.quotient (regularData.periods.quotientMap (cuspLift s, z)) := by
  change regularData.quotient
      (HolomorphicPeriodMap.periodPullbackMap data.periods regularData.periods
        (logBaseToRegular radius radius_le_cuspChart) (data.periods.quotientMap (s, z))) = _
  apply congrArg regularData.quotient
  exact HolomorphicPeriodMap.periodPullbackMap_quotientMap data.periods regularData.periods
    (logBaseToRegular radius radius_le_cuspChart) period_agreement (s, z)

/-- Every point of the actual nonzero fibre belongs to the complete cusp overlap. -/
theorem fibreCover_mem_overlap (s : LogBase radius) (z : ComplexPlane₂) :
    fibreCover data.correction radius s (cuspParameter_norm_lt s) z ∈
      specialCuspOverlap.source := by
  rw [specialCuspOverlap_source]
  change CuspPiece.projectionToBase specialCuspData specialBaseCover
    (fibreCover data.correction radius s (cuspParameter_norm_lt s) z) ∈ regularPatch
  apply (CuspPiece.projectionToBase_mem_regular_iff specialCuspData specialBaseCover _).mpr
  exact (projection_fibreCover data.correction radius s (cuspParameter_norm_lt s) z).trans_ne
    (exponential_ne_zero s)

/-- The original full overlap has the exact vector-cover formula, not only
the zero-section formula. -/
theorem overlap_fibreCover (s : LogBase radius) (z : ComplexPlane₂) :
    specialCuspOverlap (fibreCover data.correction radius s (cuspParameter_norm_lt s) z) =
      regularData.quotient (regularData.periods.quotientMap (cuspLift s, z)) := by
  let := CuspQuotient.chartedSpace data.correction radius data.radius_pos data.radius_lt_one
    data.holomorphic data.smallDrift
  let := regularData.chartedSpace (familyCovering regularData)
  have hx : fibreCover data.correction radius s (cuspParameter_norm_lt s) z ∈
      puncturedQuotientOpen data.correction radius := by
    change CuspQuotient.projection data.correction radius
      (fibreCover data.correction radius s (cuspParameter_norm_lt s) z) ≠ 0
    rw [projection_fibreCover]
    exact exponential_ne_zero s
  have he : (⟨fibreCover data.correction radius s (cuspParameter_norm_lt s) z, hx⟩ :
      PuncturedQuotient data.correction radius) =
      puncturedCuspCover data.correction radius (logVector s z) := by
    apply Subtype.ext
    rfl
  have h := cuspToRegularPartial_apply data regularData radius_le_cuspChart period_agreement
    (fibreCover data.correction radius s (cuspParameter_norm_lt s) z) hx
  have hrepresentative := congrArg
    (fun x : PuncturedQuotient data.correction radius =>
      (puncturedBiholomorph data regularData radius_le_cuspChart period_agreement x :
        regularData.Space)) he
  have hcover := puncturedBiholomorph_cover data regularData radius_le_cuspChart
    period_agreement (logVector s z)
  change specialCuspOverlap
      (fibreCover data.correction radius s (cuspParameter_norm_lt s) z) = _ at h
  exact h.trans (hrepresentative.trans (hcover.trans (familyMap_iteratedCover_logVector s z)))

/-- Both original vector-cover representatives give literally the same
point of the constructed threefold. -/
theorem inclusion_fibreCover (s : LogBase radius) (z : ComplexPlane₂) :
    inclusion (some none)
        (fibreCover data.correction radius s (cuspParameter_norm_lt s) z) =
      inclusion none (regularData.quotient (regularData.periods.quotientMap (cuspLift s, z))) := by
  apply (gluingData.inclusion_eq_iff (some none) none _ _).mpr
  exact ⟨fibreCover_mem_overlap s z, overlap_fibreCover s z⟩

/-- The native period torus and the regular family use the same actual
global basepoint after inclusion into the glued threefold. -/
theorem inclusion_nativeFibreMap_zero (s : LogBase radius) :
    inclusion (some none) (nativeFibreMap s 0) =
      inclusion none (regularData.fundamentalGroupBasepoint (cuspLift s)) := by
  have hz : nativeFibreMap s 0 =
      fibreCover data.correction radius s (cuspParameter_norm_lt s) 0 := by
    simpa only [map_zero] using nativeFibreMap_mkQ s 0
  rw [hz, inclusion_fibreCover]
  change inclusion none (regularData.quotient (regularData.periods.quotientMap (cuspLift s, 0))) =
    inclusion none (regularData.quotient (cuspLift s, 0))
  simp only [HolomorphicPeriodMap.quotientMap, map_zero]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching
