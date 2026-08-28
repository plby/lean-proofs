import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesCoordinates
import Wikipedia.HopfProblem.EllipticHigherHomologySurfaceMarked
import Wikipedia.HopfProblem.EllipticHigherHomologyHomologyNorm
import Wikipedia.HopfProblem.MappingTorusHomologyCovering

/-!
# The actual elliptic period cover and its Wang boundary

The concrete two-strip-per-period covering calculation gives the Wang
boundary of the actual product cover.  The proved period-coordinate
homeomorphism and surface homeomorphism transfer that formula to the
original period-torus covering.  Its input circle boundary is surjective,
so the primitive norm-coordinate images determine the actual cover indices.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology

/-- The previously constructed product cover is literally the cover
used in the actual finite-cover Wang calculation. -/
@[simp] theorem mappingTorusProductCover_eq_productCover (j : Kind) :
    mappingTorusProductCover j =
      Covering.productCover j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j) := rfl

/-- Both actual homology-norm definitions agree by functoriality on powers. -/
theorem fibreHomologyNorm_eq_homologyNorm (j : Kind) (n : ℕ) :
    fibreHomologyNorm j n = Covering.homologyNorm j.order (fibreTorusHomeomorph j) n :=
  (Covering.homologyNorm_eq_sum_powers j.order (fibreTorusHomeomorph j) n).symm

/-- The signed circle boundary of the original period class, after
the proved primitive integral splitting of its actual torus. -/
def surfacePeriodCoverCircleBoundary (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    SingularHomology p.val.Torus (n + 1) →ₗ[ℤ] SingularHomology (ProductTorus 3) n :=
  (circleBoundary (ProductTorus 3) n).comp
    (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1)).toLinearMap

@[simp] theorem surfacePeriodCoverCircleBoundary_apply (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology p.val.Torus (n + 1)) :
    surfacePeriodCoverCircleBoundary j p n a = circleBoundary (ProductTorus 3) n
      (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1) a) := rfl

/-- The actual split-circle boundary is onto, with no additional covering hypothesis. -/
theorem surfacePeriodCoverCircleBoundary_surjective (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Function.Surjective (surfacePeriodCoverCircleBoundary j p n) :=
  (circleBoundary_surjective (ProductTorus 3) n).comp
    (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1)).surjective

/-- The actual original finite period cover has the proved norm as its
Wang boundary in every degree.  This is a conclusion of the covering
calculation and the actual period/surface comparison maps. -/
theorem surfacePeriodCover_wangBoundary (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology p.val.Torus (n + 1)) :
    wangBoundary (fibreTorusHomeomorph j).symm n
      (surfaceMappingTorusHomologyEquiv j p (n + 1)
        (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) (n + 1) a)) =
      fibreHomologyNorm j n (surfacePeriodCoverCircleBoundary j p n a) := by
  change wangBoundary (fibreTorusHomeomorph j).symm n
    (homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) (n + 1)
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) (n + 1) a)) = _
  rw [surfaceMappingTorusHomology_periodCover, mappingTorusProductCover_eq_productCover]
  change wangBoundary (fibreTorusHomeomorph j).symm n
    (Covering.productCoverHomology j.order (fibreTorusHomeomorph j)
      (fibreTorusHomeomorph_pow_order j) (n + 1)
        (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1) a)) = _
  rw [Covering.wangBoundary_productCover_apply, ← fibreHomologyNorm_eq_homologyNorm]
  rfl

end Wikipedia.HopfProblem.Elliptic.HigherHomology
