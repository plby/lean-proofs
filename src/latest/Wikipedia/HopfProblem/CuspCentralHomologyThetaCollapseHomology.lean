import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseBelt
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseCharacters
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseLinear

/-!
# Surjectivity of the actual theta-character collapse in degree two

The three prescribed target-circle classes have explicit phase-lattice
preimages with sum zero. Actual coordinate-circle homology classes turn
those vectors into genuine midpoint classes in the source belt. They
lie in the actual Mayer--Vietoris kernel and hence lift to source degree
two. Naturality of the actual connecting map proves surjectivity of the
literal continuous character collapse.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricComponent SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual phase classes prescribed by the explicit integral triple section. -/
def thetaBeltPhaseClasses (z : Fin 3 → ℤ) (j : Fin 3) :
    SingularHomology CompactFibreTorus 1 :=
  compactPhaseCoordinateHomology (thetaPhaseTripleSection z j)

/-- Their sum is zero in actual phase homology, by linearity of the coordinate-circle map. -/
theorem thetaBeltPhaseClasses_sum (z : Fin 3 → ℤ) :
    ∑ j, thetaBeltPhaseClasses z j = 0 := by
  change (∑ j, compactPhaseCoordinateHomology (thetaPhaseTripleSection z j)) = 0
  rw [← map_sum]
  change compactPhaseCoordinateHomology (thetaPhaseTripleSum (thetaPhaseTripleSection z)) = 0
  rw [thetaPhaseTripleSum_section, map_zero]

/-- The genuine source-belt class built from the three actual midpoint sections. -/
def thetaBeltLift (z : Fin 3 → ℤ) : SingularHomology ThetaBelt 1 :=
  thetaBeltSum (thetaBeltPhaseClasses z)

theorem thetaBeltLift_mem_ker (z : Fin 3 → ℤ) :
    leftHomologyMap thetaNorth thetaSouth 1 (thetaBeltLift z) = 0 :=
  thetaBeltSum_mem_ker (thetaBeltPhaseClasses z) (thetaBeltPhaseClasses_sum z)

/-- The actual character map has the proved determinant value on the chosen actual class. -/
theorem thetaBeltPhaseClasses_character (z : Fin 3 → ℤ) (j : Fin 3) :
    unitCircleHomologyOneEquiv
      (singularHomologyMap (thetaEdgeCharacterMap j) 1 (thetaBeltPhaseClasses z j)) =
      thetaPhaseTripleCharacters (thetaPhaseTripleSection z) j := by
  rw [thetaPhaseTripleCharacters_eq_det]
  calc
    _ = -hexagonRay (thetaEdgeIndex j) 1 * thetaPhaseTripleSection z j 0 +
        hexagonRay (thetaEdgeIndex j) 0 * thetaPhaseTripleSection z j 1 :=
      edgeCharacter_coordinateHomology (hexagonRay (thetaEdgeIndex j))
        (thetaPhaseTripleSection z j)
    _ = _ := by
      change -hexagonRay (thetaEdgeIndex j) 1 * thetaPhaseTripleSection z j 0 +
          hexagonRay (thetaEdgeIndex j) 0 * thetaPhaseTripleSection z j 1 =
        hexagonRay (thetaEdgeIndex j) 0 * thetaPhaseTripleSection z j 1 -
          hexagonRay (thetaEdgeIndex j) 1 * thetaPhaseTripleSection z j 0
      ring

/-- The actual restricted collapse sends the constructed source-belt class to its prescribed
three circle coordinates. -/
theorem thetaBeltLift_image (z : Fin 3 → ℤ) :
    thetaTargetBeltHomologyEquiv (singularHomologyMap thetaBeltMap 1 (thetaBeltLift z)) = z := by
  rw [thetaBeltLift, thetaBeltMap_homologyOne_sum]
  funext j
  rw [thetaBeltPhaseClasses_character, thetaPhaseTripleCharacters_section]

/-- Every actual target-belt class has a preimage in the actual source Mayer--Vietoris kernel. -/
theorem thetaBelt_kernel_lifts (b : SingularHomology (Suspension.middleBand ThreeCircles) 1) :
    ∃ c : SingularHomology ThetaBelt 1,
      leftHomologyMap thetaNorth thetaSouth 1 c = 0 ∧
        singularHomologyMap thetaBeltMap 1 c = b := by
  refine ⟨thetaBeltLift (thetaTargetBeltHomologyEquiv b), thetaBeltLift_mem_ker _, ?_⟩
  apply thetaTargetBeltHomologyEquiv.injective
  exact thetaBeltLift_image (thetaTargetBeltHomologyEquiv b)

/-- The literal continuous phase-character collapse is surjective on actual integral `H₂`. -/
theorem thetaCharacterCollapse_homologyTwo_surjective :
    Function.Surjective (singularHomologyMap thetaCharacterCollapse 2) :=
  contractibleTargetCoverMap_homology_surjective
    (CompactFibreTorus × Theta) ThreeCircleSuspension
    thetaCharacterCollapse thetaNorth thetaSouth Suspension.northOpen Suspension.southOpen
    thetaNorth_isOpen thetaSouth_isOpen theta_open_cover
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover
    thetaCharacterCollapse_mapsTo_north thetaCharacterCollapse_mapsTo_south 1
    thetaBelt_kernel_lifts

theorem thetaCharacterCollapse_homologyTwo_range :
    LinearMap.range (singularHomologyMap thetaCharacterCollapse 2) = ⊤ :=
  LinearMap.range_eq_top.mpr thetaCharacterCollapse_homologyTwo_surjective

end Wikipedia.HopfProblem.CuspCentralHomology
