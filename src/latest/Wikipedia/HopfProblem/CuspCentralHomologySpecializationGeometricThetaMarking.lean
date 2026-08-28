import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricBaseLoops
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricEdges
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricPathClasses
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricThetaPaths

/-!
# The actual theta edge cycles have the original base-period marking

The three literal edge paths admit affine lifts with a common starting
point in the original marked base plane.  Their differences from the
third edge have periods `(-1,0)` and `(0,1)`.  Comparing actual path chains
modulo actual two-boundaries proves the singular-homology marking; no
cellular model or intersection-number formula is assumed.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCentralHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The actual torus-valued edge path is its projected affine segment,
with endpoint proof casts having no effect on its actual chain class. -/
theorem thetaEdgePath_base_pathClass (j : Fin 3) :
    pathClass ((thetaEdgePath j).map thetaBaseMap.continuous) =
      pathClass (projectedSegment (thetaEdgeBaseStart 0)
        (thetaEdgeBaseStart 0 + thetaEdgeBaseDisplacement j)) := by
  have hs : coordinateProjection 2 (thetaEdgeBaseStart 0) =
      thetaBaseMap (Suspension.north : Theta) := by
    have h := thetaBaseMap_mk_affine_commonStart (0 : unitInterval) j
    simpa only [Suspension.mk_zero, show ((0 : unitInterval) : ℝ) = 0 from rfl,
      zero_smul, add_zero] using h.symm
  have ht : coordinateProjection 2 (thetaEdgeBaseStart 0 + thetaEdgeBaseDisplacement j) =
      thetaBaseMap (Suspension.south : Theta) := by
    have h := thetaBaseMap_mk_affine_commonStart (1 : unitInterval) j
    simpa only [Suspension.mk_one, show ((1 : unitInterval) : ℝ) = 1 from rfl,
      one_smul] using h.symm
  have hp : (((thetaEdgePath j).map thetaBaseMap.continuous).cast hs ht) =
      projectedSegment (thetaEdgeBaseStart 0)
        (thetaEdgeBaseStart 0 + thetaEdgeBaseDisplacement j) := by
    apply Path.ext
    funext t
    change thetaBaseMap (Suspension.mk t j) =
      projectedSegment (thetaEdgeBaseStart 0)
        (thetaEdgeBaseStart 0 + thetaEdgeBaseDisplacement j) t
    rw [projectedSegment_apply_add, thetaBaseMap_mk_affine_commonStart]
  simpa only [pathClass_cast] using congrArg pathClass hp

/-- The integer periods of the edge differences, in the original base coordinates. -/
def thetaEdgeDifferenceVector (j : Fin 3) : Fin 2 → ℤ :=
  ![![-1, 0], ![0, 1], ![0, 0]] j

/-- Subtracting the third actual edge gives exactly its genuine period-loop
class, including its integral sign. -/
theorem thetaEdgePath_base_pathClass_sub_two (j : Fin 3) :
    pathClass ((thetaEdgePath j).map thetaBaseMap.continuous) -
        pathClass ((thetaEdgePath 2).map thetaBaseMap.continuous) =
      homologyToChainClass (ProductTorus 2) (coordinateH1 2 (thetaEdgeDifferenceVector j)) := by
  rw [thetaEdgePath_base_pathClass, thetaEdgePath_base_pathClass, coordinateH1_two_apply]
  apply projectedSegment_pathClass_sub_of_eq_add_integer
  have hd := thetaEdgeBaseDisplacement_sub_two j
  change thetaEdgeBaseDisplacement j - thetaEdgeBaseDisplacement 2 =
    (fun i => (thetaEdgeDifferenceVector j i : ℝ)) at hd
  rw [sub_eq_iff_eq_add] at hd
  rw [hd]
  abel

theorem thetaEdgeDifferenceVector_sum (m : Fin 3 → ℤ) :
    (∑ j, m j • thetaEdgeDifferenceVector j) = thetaEdgeCycleLattice m := by
  funext i
  fin_cases i <;>
    simp [Fin.sum_univ_three, thetaEdgeDifferenceVector, thetaEdgeCycleLattice]

/-- The original theta inclusion sends the actual weighted edge cycle to
the corresponding actual integral period class, not to an assigned coordinate. -/
theorem thetaBaseMap_thetaEdgeHomology (m : Fin 3 → ℤ) (hm : ∑ j, m j = 0) :
    singularHomologyMap thetaBaseMap 1 (thetaEdgeHomology m hm) =
      coordinateH1 2 (thetaEdgeCycleLattice m) := by
  apply homologyToChainClass_injective (ProductTorus 2)
  change homologyToChainClass (ProductTorus 2)
    (inducedHomology thetaBaseMap (thetaEdgeHomology m hm)) = _
  rw [homologyToChainClass_naturality, thetaEdgeHomology_chainClass, map_sum]
  have hmap (j : Fin 3) : inducedOpchains thetaBaseMap (pathClass (thetaEdgePath j)) =
      pathClass ((thetaEdgePath j).map thetaBaseMap.continuous) := by
    simp only [pathClass, inducedOpchains_chainClass, inducedChain_pathChain]
  simp_rw [map_zsmul, hmap]
  calc
    _ = ∑ j, m j • (pathClass ((thetaEdgePath j).map thetaBaseMap.continuous) -
        pathClass ((thetaEdgePath 2).map thetaBaseMap.continuous)) := by
      have hz : (∑ j, m j • pathClass
          ((thetaEdgePath 2).map thetaBaseMap.continuous)) = 0 := by
        have h := congrArg (fun n : ℤ => n • pathClass
          ((thetaEdgePath 2).map thetaBaseMap.continuous)) hm
        simpa only [Fin.sum_univ_three, add_zsmul, zero_zsmul] using h
      simp only [zsmul_sub, Finset.sum_sub_distrib, hz, sub_zero]
    _ = ∑ j, m j • homologyToChainClass (ProductTorus 2)
        (coordinateH1 2 (thetaEdgeDifferenceVector j)) := by
      simp_rw [thetaEdgePath_base_pathClass_sub_two]
    _ = homologyToChainClass (ProductTorus 2)
        (coordinateH1 2 (∑ j, m j • thetaEdgeDifferenceVector j)) := by
      simp only [map_sum, map_zsmul]
    _ = _ := by rw [thetaEdgeDifferenceVector_sum]

/-- The uniquely specified zero-sum coefficients represent the original
marked base vector in actual first singular homology. -/
theorem thetaBaseMap_thetaEdgeCoefficients (β : Fin 2 → ℤ) :
    singularHomologyMap thetaBaseMap 1
      (thetaEdgeHomology (thetaEdgeCycleCoefficients β) (thetaEdgeCycleCoefficients_sum β)) =
        loopHomologyClass (coordinatePeriodLoop 2 β) := by
  rw [thetaBaseMap_thetaEdgeHomology, thetaEdgeCycleLattice_coefficients,
    coordinateH1_two_apply]

end Wikipedia.HopfProblem.CuspCentralHomology
