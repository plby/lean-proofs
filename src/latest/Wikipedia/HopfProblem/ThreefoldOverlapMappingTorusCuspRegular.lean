import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusSpaces

/-!
# The actual cusp boundary map into the regular family

The original whole-family cusp comparison identifies every boundary
representative with its logarithmic base lift and its unchanged real
period coordinate.  The equality of period matrices is the previously
proved equality for the actual global special periods.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Cusp

open SpecialPeriods SpecialPeriods.Threefold Triangle CuspUniformization CuspFamily

/-- The original regular special-period data, with no additional choice of marking. -/
def boundaryRegularData : TrianglePeriodFamily.Data ℂ TriangleRegularPoint :=
  TrianglePeriodFamily.regularData specialPeriodMap
    specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The actual selected cusp radius lies in the proved geometric cusp chart. -/
theorem specialRadius_cap : specialData.radius ≤ cuspRadius width :=
  specialBaseCover_cusp_radius_bounds.2.2.le

/-- The original period columns agree throughout this whole logarithmic overlap. -/
theorem specialPeriod_agreement (s : LogBase specialData.radius) :
    boundaryRegularData.periods.point
        (logBaseToRegular specialData.radius specialRadius_cap s) =
      specialData.periods.point s :=
  CuspGlobalOverlap.spherePeriod_agreement triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo (specialBaseCover.radius none)
    (specialBaseCover.radius_pos none) specialCuspRadius_le specialRadius_cap s

/-- The actual global overlap map is the original native cusp overlap. -/
theorem puncturedPieceToRegular_cusp (x : PuncturedPiece none) :
    puncturedPieceToRegular none x = specialCuspOverlap x.val := by
  apply (inclusion_openEmbedding none).injective
  have hx : x.val ∈ specialCuspOverlap.source := by
    rw [specialCuspOverlap_source]
    exact x.property
  refine (puncturedPieceToRegular_inclusion none x).trans ?_
  change gluingData.inclusion (some none) x.val =
    gluingData.inclusion none (specialCuspOverlap x.val)
  exact (gluingData.inclusion_eq_iff (some none) none _ _).mpr ⟨hx, rfl⟩

/-- The native cusp overlap and the true logarithmic quotient-family map coincide. -/
theorem specialCuspOverlap_family (y : specialData.Space) :
    specialCuspOverlap (puncturedFamilyHomeomorph specialData y).val =
      CuspGlobalOverlap.familyMap specialData boundaryRegularData specialRadius_cap y := by
  let := specialData.chartedSpace
  let := CuspQuotient.chartedSpace specialData.correction specialData.radius
    specialData.radius_pos specialData.radius_lt_one specialData.holomorphic specialData.smallDrift
  let := boundaryRegularData.chartedSpace (CuspGlobalOverlap.familyCovering boundaryRegularData)
  change CuspGlobalOverlap.cuspToRegularPartial specialData boundaryRegularData
    specialRadius_cap specialPeriod_agreement (puncturedFamilyHomeomorph specialData y).val = _
  rw [CuspGlobalOverlap.cuspToRegularPartial_apply specialData boundaryRegularData
    specialRadius_cap specialPeriod_agreement _ (puncturedFamilyHomeomorph specialData y).property]
  change CuspGlobalOverlap.familyMap specialData boundaryRegularData specialRadius_cap
    (specialData.puncturedFamilyBiholomorph.symm (specialData.puncturedFamilyBiholomorph y)) = _
  rw [Diffeomorph.symm_apply_apply]

/-- The actual cusp coefficient on every real-cylinder representative keeps the
original rank-four real period coordinate exactly. -/
theorem boundaryToRegularFamily_cusp_mk (t : ℝ) (x : RealTorus₄) :
    boundaryToRegularFamily none (MappingTorus.mk monodromy (t, x)) =
      boundaryRegularData.quotient
        (logBaseToRegular specialData.radius specialRadius_cap
          (logPoint specialData.radius specialData.radius_pos t specialHeight), x) := by
  let p : PuncturedPiece none :=
    specialBoundaryInclusion (MappingTorus.mk monodromy (t, x))
  have hp : boundaryToRegularFamily none (MappingTorus.mk monodromy (t, x)) =
      specialCuspOverlap p.val := puncturedPieceToRegular_cusp p
  refine hp.trans ?_
  change specialCuspOverlap (boundaryCylinder specialData specialHeight (t, x)).val = _
  rw [boundaryCylinder_apply, specialCuspOverlap_family, CuspGlobalOverlap.familyMap_quotient]

/-- The same statement in the actual original integral-lattice coordinates. -/
theorem boundaryToRegularFamily_cusp_realCoordinates (t : ℝ) (x : RealPlane₄) :
    boundaryToRegularFamily none
        (MappingTorus.mk monodromy (t, standardLattice.mkQ x)) =
      boundaryRegularData.quotient
        (logBaseToRegular specialData.radius specialRadius_cap
          (logPoint specialData.radius specialData.radius_pos t specialHeight),
          standardLattice.mkQ x) :=
  boundaryToRegularFamily_cusp_mk t (standardLattice.mkQ x)

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Cusp
