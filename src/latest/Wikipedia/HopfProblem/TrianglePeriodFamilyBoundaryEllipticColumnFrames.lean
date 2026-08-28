import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCanonicalFrames
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeCylinder
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticTailHomology

/-!
# The actual elliptic boundary-column frames

The whole native lifted square and the canonical quarter-time lifts give
the exact same deck frame at both intersection columns.  This frame
retains the original analytic tail.  Its inverse is proved to fix actual
Wang-boundary classes, using the actual affine monodromy and the previously
proved cyclic centralizer calculation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Meridians Homology Elliptic
open SpecialPeriods.Threefold.EllipticGeometry
open SingularMayerVietoris PeriodTorusHigherHomology BoundaryCircleSlits

/-- The real phase for which the actual positive boundary uses the fixed slit cover. -/
def ellipticBoundaryPhase (j : Kind) : ℝ := circlePhase (attachingMeridianIndex j)

/-- The source generator agrees with the generator of the actual selected meridian. -/
theorem ellipticBoundary_generator (j : Kind) :
    compatibleMeridianGenerator (attachingMeridianIndex j) = ellipticGenerator j := by
  cases j <;> rfl

/-- The common column frame includes both the actual analytic tail and
the inverse-generator frame of the canonical upper-slit section. -/
def ellipticBoundaryFrame (j : Kind) : TriangleGroup :=
  nativeTailFrame j * (ellipticGenerator j)⁻¹

/-- The endpoint of the entire original lifted square is the actual
phased canonical curve, with the literal tail frame retained. -/
theorem nativeShiftedSquareLift_canonical (j : Kind) (t : ℝ) :
    nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, t) =
      nativeTailFrame j • canonicalPhasedLift (attachingMeridianIndex j) t :=
  nativeShiftedSquareLift_final j (ellipticBoundaryPhase j) t

/-- The actual quarter-time base point has the full common column frame. -/
theorem nativeShiftedSquareLift_quarter_frame (j : Kind) :
    nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4) =
      ellipticBoundaryFrame j • upperLiftOnOverlap normalizedSlitBaseLift
        (canonicalQuarterOverlapIndex (attachingMeridianIndex j))
        (canonicalQuarterOverlapPoint (attachingMeridianIndex j)) := by
  rw [nativeShiftedSquareLift_canonical, canonicalPhasedLift_quarter_frame,
    ellipticBoundary_generator, ellipticBoundaryFrame, mul_smul]

/-- The actual three-quarter-time point has precisely the same full frame. -/
theorem nativeShiftedSquareLift_threeQuarter_frame (j : Kind) :
    nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4) =
      ellipticBoundaryFrame j • upperLiftOnOverlap normalizedSlitBaseLift
        (canonicalThreeQuarterOverlapIndex (attachingMeridianIndex j))
        (canonicalThreeQuarterOverlapPoint (attachingMeridianIndex j)) := by
  rw [nativeShiftedSquareLift_canonical, canonicalPhasedLift_threeQuarter_frame,
    ellipticBoundary_generator, ellipticBoundaryFrame, mul_smul]

/-- The first actual column projects to the exact canonical overlap point. -/
theorem nativeShiftedSquareLift_quarter_project (j : Kind) :
    triangleRegularProject
        (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4)) =
      (canonicalQuarterOverlapPoint (attachingMeridianIndex j)).val := by
  rw [nativeShiftedSquareLift_canonical, triangleRegularProject_covering.map_smul,
    canonicalPhasedLift_quarter_project]

/-- The second actual column likewise retains its exact projected overlap point. -/
theorem nativeShiftedSquareLift_threeQuarter_project (j : Kind) :
    triangleRegularProject
        (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4)) =
      (canonicalThreeQuarterOverlapPoint (attachingMeridianIndex j)).val := by
  rw [nativeShiftedSquareLift_canonical, triangleRegularProject_covering.map_smul,
    canonicalPhasedLift_threeQuarter_project]

/-- The full inverse column frame fixes every actual Wang-boundary class;
the analytic tail has not been discarded or replaced by an assumed frame. -/
theorem ellipticBoundaryFrame_inv_wangBoundary (j : Kind) (v : Lattice) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus (flatTorusAffine j v)) (n + 1)) :
    triangleHomologyEquiv (ellipticBoundaryFrame j)⁻¹ n
        (MappingTorusHomology.wangBoundary (flatTorusAffine j v) n a) =
      MappingTorusHomology.wangBoundary (flatTorusAffine j v) n a := by
  rw [ellipticBoundaryFrame, mul_inv_rev, inv_inv, triangleHomologyEquiv_mul_apply,
    nativeTailFrame_inv_wangBoundary, ellipticWangBoundary_generator_fixed]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
