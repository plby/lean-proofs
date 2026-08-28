import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspCover
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspWang
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryAffineColumns

/-!
# The genuine two cusp intersection columns

Both actual quarter-time maps have the same upper-chart frame: the
geometrically constructed analytic tail followed by the first source
generator.  The literal fibre coordinate is unchanged.  This gives the
whole singular-homology coefficient before any simplification.  The
proved cusp centralizer then removes only the tail, and only on genuine
Wang-boundary classes.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle Homology
open ThreefoldOverlapMappingTorus.Cusp SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual first column, with its complete geometrically determined frame. -/
theorem lowerColumn_homology (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    Homology.intersectionHomologyEquiv boundaryRegularData normalizedSlitBaseLift n
        (singularHomologyMap lowerColumn n a) =
      componentCoordinates 1
        (triangleHomologyEquiv (tailFrame * triangleGenerator₁)⁻¹ n a) := by
  rw [intersectionHomology_componentMap boundaryRegularData normalizedSlitBaseLift
    lowerColumn 1 lowerColumn_mem n a]
  have h := componentFibreMap_homology_deck_comp boundaryRegularData normalizedSlitBaseLift
    lowerColumn 1 lowerColumn_mem outerClockwiseQuarterPoint
    (nativeLiftedSquare (1, 1 / 4)) (tailFrame * triangleGenerator₁)
    nativeLiftedSquare_quarter_frame (ContinuousMap.id RealTorus₄) lowerColumn_coe n
  rw [h, singularHomologyMap_id, LinearMap.comp_apply, LinearMap.id_apply]
  rfl

/-- The actual second column retains precisely the same complete frame. -/
theorem upperColumn_homology (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    Homology.intersectionHomologyEquiv boundaryRegularData normalizedSlitBaseLift n
        (singularHomologyMap upperColumn n a) =
      componentCoordinates 2
        (triangleHomologyEquiv (tailFrame * triangleGenerator₁)⁻¹ n a) := by
  rw [intersectionHomology_componentMap boundaryRegularData normalizedSlitBaseLift
    upperColumn 2 upperColumn_mem n a]
  have h := componentFibreMap_homology_deck_comp boundaryRegularData normalizedSlitBaseLift
    upperColumn 2 upperColumn_mem outerClockwiseThreeQuarterPoint
    (nativeLiftedSquare (1, 3 / 4)) (tailFrame * triangleGenerator₁)
    nativeLiftedSquare_threeQuarters_frame (ContinuousMap.id RealTorus₄) upperColumn_coe n
  rw [h, singularHomologyMap_id, LinearMap.comp_apply, LinearMap.id_apply]
  rfl

/-- The actual left crossing coefficient on a genuine cusp Wang class. -/
theorem lowerColumn_wangBoundary (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus monodromy) (n + 1)) :
    Homology.intersectionHomologyEquiv boundaryRegularData normalizedSlitBaseLift n
        (singularHomologyMap lowerColumn n
          (MappingTorusHomology.wangBoundary monodromy n a)) =
      componentCoordinates 1
        (triangleHomologyEquiv triangleGenerator₁⁻¹ n
          (MappingTorusHomology.wangBoundary monodromy n a)) := by
  rw [lowerColumn_homology,
    commutingColumnFrame_inv_wangBoundary tailFrame tailFrame_commute]

/-- The actual right crossing coefficient is the same class in the other component. -/
theorem upperColumn_wangBoundary (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus monodromy) (n + 1)) :
    Homology.intersectionHomologyEquiv boundaryRegularData normalizedSlitBaseLift n
        (singularHomologyMap upperColumn n
          (MappingTorusHomology.wangBoundary monodromy n a)) =
      componentCoordinates 2
        (triangleHomologyEquiv triangleGenerator₁⁻¹ n
          (MappingTorusHomology.wangBoundary monodromy n a)) := by
  rw [upperColumn_homology,
    commutingColumnFrame_inv_wangBoundary tailFrame tailFrame_commute]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
