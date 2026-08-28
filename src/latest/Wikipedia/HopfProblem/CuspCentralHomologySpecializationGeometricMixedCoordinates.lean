import Wikipedia.HopfProblem.CuspCentralHomologySpecializationKernelMap
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricBaseLoops
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarkingProductTorus
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductNaturality

/-!
# Actual mixed cross products in the original source exterior marking

The base factor is crossed with the compact phase factor in that order.
The actual swap into the phase--base product is followed by the existing
source-coordinate homeomorphism, whose output order is base--phase.
Factoring this composite through actual addition proves the exterior
marking with its sign; no interchange sign is assumed.
-/

noncomputable section

open scoped Matrix ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction FirstHurewicz SingularMayerVietoris
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin SpecializationModel

/-- The first two coordinates are the marked base periods. -/
def mixedBaseMatrix : Matrix (Fin 4) (Fin 2) ℤ :=
  !![1, 0; 0, 1; 0, 0; 0, 0]

/-- The last two coordinates are the marked integer phase periods. -/
def mixedPhaseMatrix : Matrix (Fin 4) (Fin 2) ℤ :=
  !![0, 0; 0, 0; 1, 0; 0, 1]

theorem mixedBaseMatrix_mulVec (β : Fin 2 → ℤ) :
    mixedBaseMatrix *ᵥ β = ![β 0, β 1, 0, 0] := by
  funext i
  fin_cases i <;> simp [mixedBaseMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mixedPhaseMatrix_mulVec (v : Fin 2 → ℤ) :
    mixedPhaseMatrix *ᵥ v = ![0, 0, v 0, v 1] := by
  funext i
  fin_cases i <;> simp [mixedPhaseMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def mixedBaseInclusion : C(ProductTorus 2, ProductTorus 4) :=
  torusMatrixMap mixedBaseMatrix

def mixedPhaseInclusion : C(CompactFibreTorus, ProductTorus 4) :=
  (torusMatrixMap mixedPhaseMatrix).comp
    (compactFibreTorusHomeomorph : C(CompactFibreTorus, ProductTorus 2))

@[simp] theorem mixedBaseInclusion_apply (x : ProductTorus 2) :
    mixedBaseInclusion x = ![x 0, x 1, 0, 0] := by
  funext i
  fin_cases i <;> simp [mixedBaseInclusion, torusMatrixMap_apply, mixedBaseMatrix,
    Fin.sum_univ_two]

@[simp] theorem mixedPhaseInclusion_apply (u : CompactFibreTorus) :
    mixedPhaseInclusion u =
      ![0, 0, compactFibreTorusHomeomorph u 0, compactFibreTorusHomeomorph u 1] := by
  funext i
  fin_cases i <;> simp [mixedPhaseInclusion, torusMatrixMap_apply, mixedPhaseMatrix,
    Fin.sum_univ_two]

/-- The actual swap followed by the original source marking. -/
def mixedCoordinatesMap : C(ProductTorus 2 × CompactFibreTorus, ProductTorus 4) :=
  (sourceProductCoordinateHomeomorph :
    C(CompactFibreTorus × ProductTorus 2, ProductTorus 4)).comp
      (swapMap (ProductTorus 2) CompactFibreTorus)

theorem mixedCoordinatesMap_eq_addition :
    mixedCoordinatesMap = (additionMap (ProductTorus 4)).comp
      (mixedBaseInclusion.prodMap mixedPhaseInclusion) := by
  apply ContinuousMap.ext
  intro p
  change sourceProductCoordinateHomeomorph (p.2, p.1) =
    mixedBaseInclusion p.1 + mixedPhaseInclusion p.2
  rw [sourceProductCoordinateHomeomorph_apply, mixedBaseInclusion_apply,
    mixedPhaseInclusion_apply]
  funext i
  fin_cases i <;> simp

/-- Naturality identifies the actual cross product with the ordered
Pontryagin product of the two actual factor inclusions. -/
theorem mixedCoordinatesMap_cross
    (a : SingularHomology (ProductTorus 2) 1)
    (b : SingularHomology CompactFibreTorus 1) :
    singularHomologyMap mixedCoordinatesMap 2
        (crossProductHomology (ProductTorus 2) CompactFibreTorus 1 a b) =
      product11 (ProductTorus 4)
        (singularHomologyMap mixedBaseInclusion 1 a)
        (singularHomologyMap mixedPhaseInclusion 1 b) := by
  have h := crossProductHomology_natural mixedBaseInclusion mixedPhaseInclusion 1 a b
  change singularHomologyMap (mixedBaseInclusion.prodMap mixedPhaseInclusion) 2
      (crossProductHomology (ProductTorus 2) CompactFibreTorus 1 a b) =
    crossProductHomology (ProductTorus 4) (ProductTorus 4) 1
      (singularHomologyMap mixedBaseInclusion 1 a)
      (singularHomologyMap mixedPhaseInclusion 1 b) at h
  rw [mixedCoordinatesMap_eq_addition, singularHomologyMap_comp, LinearMap.comp_apply, h]
  rfl

theorem mixedBaseInclusion_periodHomology (β : Fin 2 → ℤ) :
    singularHomologyMap mixedBaseInclusion 1
        (loopHomologyClass (coordinatePeriodLoop 2 β)) =
      loopHomologyClass (coordinatePeriodLoop 4 ![β 0, β 1, 0, 0]) := by
  change inducedHomology (torusMatrixMap mixedBaseMatrix)
    (loopHomologyClass (coordinatePeriodLoop 2 β)) = _
  rw [torusMatrixMap_coordinatePeriodHomology, mixedBaseMatrix_mulVec]

/-- The ordered compact-phase marking is the class of the actual straight
period loop in the two additive circle coordinates. -/
theorem compactPhaseCoordinateHomology_coordinates (v : Fin 2 → ℤ) :
    singularHomologyMap
      (compactFibreTorusHomeomorph : C(CompactFibreTorus, ProductTorus 2)) 1
      (compactPhaseCoordinateHomology v) =
      loopHomologyClass (coordinatePeriodLoop 2 v) := by
  have hi (i : Fin 2) :
      singularHomologyMap
        (compactFibreTorusHomeomorph : C(CompactFibreTorus, ProductTorus 2)) 1
        (compactPhaseCoordinateClass i) =
        loopHomologyClass (coordinatePeriodLoop 2 (Pi.single i 1)) :=
    compactPhaseCircleMap_positiveHomology (Pi.single i 1)
  calc
    singularHomologyMap
        (compactFibreTorusHomeomorph : C(CompactFibreTorus, ProductTorus 2)) 1
        (compactPhaseCoordinateHomology v) =
        v 0 • loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 0 1)) +
          v 1 • loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 1 1)) := by
      rw [compactPhaseCoordinateHomology_apply, map_add, map_zsmul, map_zsmul, hi 0, hi 1]
    _ = coordinateH1 2 v := by
      change _ = ∑ i : Fin 2, v i • loopHomologyClass (coordinatePeriodLoop 2 (Pi.single i 1))
      rw [Fin.sum_univ_two]
    _ = loopHomologyClass (coordinatePeriodLoop 2 v) := coordinateH1_two_apply v

/-- Bundled compatibility with the actual positive coordinate-loop linear map. -/
theorem compactPhaseCoordinateHomology_coordinates_comp :
    (singularHomologyMap
      (compactFibreTorusHomeomorph : C(CompactFibreTorus, ProductTorus 2)) 1).comp
      compactPhaseCoordinateHomology = coordinateH1 2 := by
  apply LinearMap.ext
  intro v
  exact (compactPhaseCoordinateHomology_coordinates v).trans (coordinateH1_two_apply v).symm

/-- Every marked integral phase class is the positive generator pushed
through the literal compact-phase circle with that same vector. -/
theorem compactPhaseCoordinateHomology_eq_circleMap (v : Fin 2 → ℤ) :
    compactPhaseCoordinateHomology v =
      singularHomologyMap (compactPhaseCircleMap v) 1 (unitCircleHomologyOneEquiv.symm 1) := by
  apply (homeomorphHomologyEquiv compactFibreTorusHomeomorph 1).injective
  exact (compactPhaseCoordinateHomology_coordinates v).trans
    (compactPhaseCircleMap_positiveHomology v).symm

theorem mixedPhaseInclusion_periodHomology (v : Fin 2 → ℤ) :
    singularHomologyMap mixedPhaseInclusion 1 (compactPhaseCoordinateHomology v) =
      loopHomologyClass (coordinatePeriodLoop 4 ![0, 0, v 0, v 1]) := by
  rw [mixedPhaseInclusion, singularHomologyMap_comp, LinearMap.comp_apply,
    compactPhaseCoordinateHomology_coordinates]
  change inducedHomology (torusMatrixMap mixedPhaseMatrix)
    (loopHomologyClass (coordinatePeriodLoop 2 v)) = _
  rw [torusMatrixMap_coordinatePeriodHomology, mixedPhaseMatrix_mulVec]

/-- The actual mixed product has the positive `β ∧ α` marking.  This
identity uses the displayed continuous maps, not an assumed swap sign. -/
theorem mixedCoordinatesMap_periodCross (β v : Fin 2 → ℤ) :
    singularHomologyMap mixedCoordinatesMap 2
        (crossProductHomology (ProductTorus 2) CompactFibreTorus 1
          (loopHomologyClass (coordinatePeriodLoop 2 β)) (compactPhaseCoordinateHomology v)) =
      coordinateTorusWedgeTwo
        (exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]]) := by
  rw [mixedCoordinatesMap_cross, mixedBaseInclusion_periodHomology,
    mixedPhaseInclusion_periodHomology]
  exact (coordinateTorusWedgeTwo_apply_ιMulti_periodLoops (Elliptic.examplePeriod .four)
    ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]]).symm

/-- Keeping the actual swap and the actual phase--base homeomorphism
separate gives the same signed mixed exterior class. -/
theorem sourceProductCoordinateHomeomorph_swappedCross (β v : Fin 2 → ℤ) :
    homeomorphHomologyEquiv sourceProductCoordinateHomeomorph 2
        (singularHomologyMap (swapMap (ProductTorus 2) CompactFibreTorus) 2
          (crossProductHomology (ProductTorus 2) CompactFibreTorus 1
            (loopHomologyClass (coordinatePeriodLoop 2 β)) (compactPhaseCoordinateHomology v))) =
      coordinateTorusWedgeTwo
        (exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]]) := by
  change ((singularHomologyMap
      (sourceProductCoordinateHomeomorph : C(CompactFibreTorus × ProductTorus 2, ProductTorus 4))
      2).comp (singularHomologyMap (swapMap (ProductTorus 2) CompactFibreTorus) 2))
      (crossProductHomology (ProductTorus 2) CompactFibreTorus 1
        (loopHomologyClass (coordinatePeriodLoop 2 β)) (compactPhaseCoordinateHomology v)) = _
  rw [← singularHomologyMap_comp]
  exact mixedCoordinatesMap_periodCross β v

theorem mixedCoordinatesMap_periodCross_exterior (β v : Fin 2 → ℤ) :
    coordinateTorusH2ExteriorEquiv
        (singularHomologyMap mixedCoordinatesMap 2
          (crossProductHomology (ProductTorus 2) CompactFibreTorus 1
            (loopHomologyClass (coordinatePeriodLoop 2 β)) (compactPhaseCoordinateHomology v))) =
      exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]] := by
  rw [mixedCoordinatesMap_periodCross, coordinateTorusH2ExteriorEquiv_wedge]

/-- Applying the original marked collapse to the mixed exterior class is
exactly applying the original product collapse to the swapped actual cross. -/
theorem markedCollapse_mixedCoordinates
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (β v : Fin 2 → ℤ) :
    singularHomologyMap (markedCollapse C ε hε) 2
        (coordinateTorusWedgeTwo
          (exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]])) =
      singularHomologyMap (productCollapse C ε hε) 2
        (singularHomologyMap (swapMap (ProductTorus 2) CompactFibreTorus) 2
          (crossProductHomology (ProductTorus 2) CompactFibreTorus 1
            (loopHomologyClass (coordinatePeriodLoop 2 β)) (compactPhaseCoordinateHomology v))) := by
  rw [← sourceProductCoordinateHomeomorph_swappedCross]
  exact markedCollapse_homology_product C ε hε 2 _

end Wikipedia.HopfProblem.CuspCentralHomology
