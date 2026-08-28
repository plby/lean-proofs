import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricMixedCoordinates
import Wikipedia.HopfProblem.CuspCentralCohomologySlopeForm

/-!
# Mixed products in the ordered six-coordinate homology basis

The actual base--phase cross products are identified with the four mixed
positions of the existing integral exterior-square coordinates.  The two
pure positions vanish, and the four positive unit products give positions
`1, 2, 3, 4` without a sign change.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction FirstHurewicz SingularMayerVietoris
open PeriodTorusHigherHomology PeriodTorusHigherHomologyExterior LocalSystemMatrices

/-- The ordered minors of the literal base--phase decomposable vector. -/
theorem mixedWedge_squareCoordinates (β v : Fin 2 → ℤ) :
    squareCoordinates
        (exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]]) =
      CuspCentralCohomology.mixedPeriodCoordinates β v := by
  funext i
  rw [squareCoordinates_apply, squareBasis, Module.Basis.repr_reindex_apply]
  change ((Pi.basisFun ℤ (Fin 4)).exteriorPower 2).repr
    (exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]])
    (pairSubset i) = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [pairSubset_ordered, Module.Basis.coord_apply, Pi.basisFun_repr]
  fin_cases i <;>
    simp [pairIndices, CuspCentralCohomology.mixedPeriodCoordinates, Matrix.det_fin_two]

/-- The actual mixed wedge has the four displayed mixed integer coordinates. -/
theorem mixedWedge_homologyCoordinates (β v : Fin 2 → ℤ) :
    coordinateTorusH2Coordinates
        (coordinateTorusWedgeTwo
          (exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]])) =
      CuspCentralCohomology.mixedPeriodCoordinates β v := by
  change squareCoordinates
    (coordinateTorusH2ExteriorEquiv
      (coordinateTorusWedgeTwo
        (exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]]))) = _
  rw [coordinateTorusH2ExteriorEquiv_wedge]
  exact mixedWedge_squareCoordinates β v

/-- The inverse-coordinate form of the same actual homology identity. -/
theorem mixedWedge_eq_coordinates_symm (β v : Fin 2 → ℤ) :
    coordinateTorusWedgeTwo
        (exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]]) =
      coordinateTorusH2Coordinates.symm (CuspCentralCohomology.mixedPeriodCoordinates β v) := by
  apply coordinateTorusH2Coordinates.injective
  rw [mixedWedge_homologyCoordinates, LinearEquiv.apply_symm_apply]

/-- This is also the coordinate vector of the actual transported cross product. -/
theorem mixedCoordinatesMap_periodCross_coordinates (β v : Fin 2 → ℤ) :
    coordinateTorusH2Coordinates
        (singularHomologyMap mixedCoordinatesMap 2
          (crossProductHomology (ProductTorus 2) CompactFibreTorus 1
            (loopHomologyClass (coordinatePeriodLoop 2 β)) (compactPhaseCoordinateHomology v))) =
      CuspCentralCohomology.mixedPeriodCoordinates β v := by
  rw [mixedCoordinatesMap_periodCross, mixedWedge_homologyCoordinates]

theorem mixedCoordinatesMap_periodCross_eq_coordinates_symm (β v : Fin 2 → ℤ) :
    singularHomologyMap mixedCoordinatesMap 2
        (crossProductHomology (ProductTorus 2) CompactFibreTorus 1
          (loopHomologyClass (coordinatePeriodLoop 2 β)) (compactPhaseCoordinateHomology v)) =
      coordinateTorusH2Coordinates.symm (CuspCentralCohomology.mixedPeriodCoordinates β v) := by
  rw [mixedCoordinatesMap_periodCross, mixedWedge_eq_coordinates_symm]

/-- The positive first base and first phase generators give position `1`. -/
theorem mixedWedge_basis00 :
    coordinateTorusWedgeTwo
        (exteriorPower.ιMulti ℤ 2 ![![1, 0, 0, 0], ![0, 0, 1, 0]]) =
      coordinateTorusH2Coordinates.symm (Pi.single 1 1) := by
  refine (mixedWedge_eq_coordinates_symm ![1, 0] ![1, 0]).trans ?_
  apply congrArg coordinateTorusH2Coordinates.symm
  funext i
  fin_cases i <;> simp [CuspCentralCohomology.mixedPeriodCoordinates]

/-- The positive first base and second phase generators give position `2`. -/
theorem mixedWedge_basis01 :
    coordinateTorusWedgeTwo
        (exteriorPower.ιMulti ℤ 2 ![![1, 0, 0, 0], ![0, 0, 0, 1]]) =
      coordinateTorusH2Coordinates.symm (Pi.single 2 1) := by
  refine (mixedWedge_eq_coordinates_symm ![1, 0] ![0, 1]).trans ?_
  apply congrArg coordinateTorusH2Coordinates.symm
  funext i
  fin_cases i <;> simp [CuspCentralCohomology.mixedPeriodCoordinates]

/-- The positive second base and first phase generators give position `3`. -/
theorem mixedWedge_basis10 :
    coordinateTorusWedgeTwo
        (exteriorPower.ιMulti ℤ 2 ![![0, 1, 0, 0], ![0, 0, 1, 0]]) =
      coordinateTorusH2Coordinates.symm (Pi.single 3 1) := by
  refine (mixedWedge_eq_coordinates_symm ![0, 1] ![1, 0]).trans ?_
  apply congrArg coordinateTorusH2Coordinates.symm
  funext i
  fin_cases i <;> simp [CuspCentralCohomology.mixedPeriodCoordinates]

/-- The positive second base and second phase generators give position `4`. -/
theorem mixedWedge_basis11 :
    coordinateTorusWedgeTwo
        (exteriorPower.ιMulti ℤ 2 ![![0, 1, 0, 0], ![0, 0, 0, 1]]) =
      coordinateTorusH2Coordinates.symm (Pi.single 4 1) := by
  refine (mixedWedge_eq_coordinates_symm ![0, 1] ![0, 1]).trans ?_
  apply congrArg coordinateTorusH2Coordinates.symm
  funext i
  fin_cases i <;> simp [CuspCentralCohomology.mixedPeriodCoordinates]

end Wikipedia.HopfProblem.CuspCentralHomology
