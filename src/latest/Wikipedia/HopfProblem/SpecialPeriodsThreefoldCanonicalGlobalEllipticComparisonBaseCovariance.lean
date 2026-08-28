import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonBaseUnits
import Wikipedia.HopfProblem.EllipticBundleCharacters

/-!
# Cyclic covariance of the actual elliptic base differential

The finite global sphere coordinate is invariant under the actual elliptic
rotation.  Differentiating its ambient expression on the native disc chart
gives the precise rotation multiplier of its derivative, including at zero.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open Triangle Elliptic

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

/-- The actual global finite coordinate is invariant under the filling's rotation. -/
theorem discCoordinate_rotation (j : Kind) (s : Disc) :
    discCoordinate j (familyRotation j s) = discCoordinate j s := by
  simp only [discCoordinate_eq_finiteProjection, EllipticFilling.neighborhoodLift_rotation]
  cases j
  · simpa only [ellipticGeneratorSL, triangleGeometricRepresentation_generator₁_apply] using
      BetaTorsor.finiteProjection_invariant triangleSphereUniformization triangleGenerator₁
        (EllipticFilling.neighborhoodLift .three s)
  · simpa only [ellipticGeneratorSL, triangleGeometricRepresentation_generator₂_apply] using
      BetaTorsor.finiteProjection_invariant triangleSphereUniformization triangleGenerator₂
        (EllipticFilling.neighborhoodLift .four s)

/-- The invariance is an equality of actual ambient germs at every disc point. -/
theorem discCoordinateExtension_rotation_eventually (j : Kind) (s : Disc) :
    (fun z : ℂ => discCoordinateExtension j (normalPhase j * z)) =ᶠ[𝓝 (s : ℂ)]
      discCoordinateExtension j := by
  have hs : (s : ℂ) ∈ (chartAt ℂ discZero).target :=
    (chartAt ℂ discZero).map_source (by trivial)
  filter_upwards [(chartAt ℂ discZero).open_target.mem_nhds hs] with z hz
  have hrot : (familyRotation j ((chartAt ℂ discZero).symm z) : ℂ) = normalPhase j * z := by
    rw [familyRotation_val, SectionsUnit.discChart_symm_coe hz]
  rw [← hrot, discCoordinateExtension_coe, discCoordinate_rotation]
  rfl

/-- The exact chain rule for the genuine elliptic base differential. -/
theorem baseDerivative_rotation (j : Kind) (s : Disc) :
    baseDerivative j (familyRotation j s) * normalPhase j = baseDerivative j s := by
  have houter : HasDerivAt (discCoordinateExtension j)
      (baseDerivative j (familyRotation j s)) (familyRotation j s : ℂ) :=
    (discCoordinateExtension_analyticAt_coe j (familyRotation j s)).differentiableAt.hasDerivAt
  have hrotation : HasDerivAt (fun z : ℂ => normalPhase j * z) (normalPhase j) (s : ℂ) :=
    hasDerivAt_const_mul (normalPhase j)
  have hcomp := houter.comp_of_eq (s : ℂ) hrotation (familyRotation_val j s)
  exact (hcomp.congr_of_eventuallyEq
    (discCoordinateExtension_rotation_eventually j s).symm).unique
      (discCoordinateExtension_analyticAt_coe j s).differentiableAt.hasDerivAt

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
