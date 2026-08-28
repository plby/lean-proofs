import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspColumns
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticSourceProjection

/-!
# The actual cusp boundary coefficient in the source kernel

Apply the proved naturality theorem for the actual smaller two-arc
mapping-torus cover and the actual regular-family slit cover.  Its two
literal crossing maps give the signed left and right components.  The
unconditional source orientation and the genuine cusp-invariance relation
then identify both source-kernel entries.  The original native attachment
map is retained through its constructed whole-boundary homotopy.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle Homology
open SingularMayerVietoris PeriodTorusHigherHomology ThreefoldOverlapMappingTorus
open ThreefoldOverlapMappingTorus.Cusp

/-- The literal original cusp coefficient in the geometrically identified
intersection components, before the source-coordinate simplification. -/
theorem boundary_sourceKernelProjection_components (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus monodromy) (n + 1)) :
    (sourceKernelProjection boundaryRegularData n
        (boundaryRegularHomologyMap none (n + 1) a) :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      normalizedSourceDomainEquiv n
        (-componentCoordinates 1
          (triangleHomologyEquiv triangleGenerator₁⁻¹ n
            (MappingTorusHomology.wangBoundary monodromy n a)) +
        componentCoordinates 2
          (triangleHomologyEquiv triangleGenerator₁⁻¹ n
            (MappingTorusHomology.wangBoundary monodromy n a))).2 := by
  refine (congrArg
    (fun z : SingularHomology boundaryRegularData.Space (n + 1) =>
      (sourceKernelProjection boundaryRegularData n z :
        SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n))
    (LinearMap.congr_fun (boundaryRegularHomologyMap_normalized (n + 1)) a)).trans ?_
  refine (RefinedWang.sourceKernelProjection_quarterColumns boundaryRegularData monodromy
    normalizedBoundaryMap normalizedBoundaryMap_upper normalizedBoundaryMap_lower n a).trans ?_
  change normalizedSourceDomainEquiv n
    (-Homology.intersectionHomologyEquiv boundaryRegularData normalizedSlitBaseLift n
      (singularHomologyMap lowerColumn n
        (MappingTorusHomology.wangBoundary monodromy n a)) +
    Homology.intersectionHomologyEquiv boundaryRegularData normalizedSlitBaseLift n
      (singularHomologyMap upperColumn n
        (MappingTorusHomology.wangBoundary monodromy n a))).2 = _
  rw [lowerColumn_wangBoundary, upperColumn_wangBoundary]

/-- The exact all-degree cusp column in the two fixed source-meridian
coordinates.  Both signs and the remaining inverse first-generator
action come from actual maps and the clockwise finite-plane peripheral loop. -/
theorem boundary_sourceKernelProjection (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus monodromy) (n + 1)) :
    (sourceKernelProjection boundaryRegularData n
        (boundaryRegularHomologyMap none (n + 1) a) :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      (-triangleHomologyEquiv triangleGenerator₁⁻¹ n
          (MappingTorusHomology.wangBoundary monodromy n a),
        -MappingTorusHomology.wangBoundary monodromy n a) := by
  rw [boundary_sourceKernelProjection_components, normalizedSourceDomainEquiv_nonpos]
  simpa only [componentCoordinates_one, componentCoordinates_two, Prod.neg_mk,
    Prod.mk_add_mk, neg_zero, zero_add, add_zero] using
    congrArg
      (fun b : SingularHomology RealTorus₄ n =>
        (-triangleHomologyEquiv triangleGenerator₁⁻¹ n
          (MappingTorusHomology.wangBoundary monodromy n a), -b))
      (wangBoundary_inverse_word n a)

/-- Degree four, the actual cusp column needed by the fifth global
homology calculation, with no chosen middle splitting. -/
theorem boundary_four_sourceKernelProjection
    (a : SingularHomology (MappingTorus.Torus monodromy) 4) :
    (sourceKernelProjection boundaryRegularData 3
        (boundaryRegularHomologyMap none 4 a) :
      SingularHomology RealTorus₄ 3 × SingularHomology RealTorus₄ 3) =
      (-triangleHomologyEquiv triangleGenerator₁⁻¹ 3
          (MappingTorusHomology.wangBoundary monodromy 3 a),
        -MappingTorusHomology.wangBoundary monodromy 3 a) :=
  boundary_sourceKernelProjection 3 a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
