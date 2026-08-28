import Wikipedia.HopfProblem.CuspCentralHomologySpecializationBoundary
import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasisGeometric
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseHomology

/-!
# The geometric boundary contribution to specialization

The actual theta-product Mayer--Vietoris connecting map records three phase
classes.  Naturality sends each one through the character of its actual
hexagon edge.  The constructed boundary homotopy then identifies their images
under specialization with the oriented fundamental classes of the three
actual central double curves.

All classes in the source are genuine singular-homology classes.  In
particular, zero-sum belt data are lifted using the exact Mayer--Vietoris
sequence, not by prescribing the image in the target marking.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricComponent CuspRetraction CuspCollapse SpecializationModel
open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual connecting map for the north/south cover of the phase--theta product. -/
abbrev thetaConnecting :=
  connectingHomomorphism thetaNorth thetaSouth
    thetaNorth_isOpen thetaSouth_isOpen theta_open_cover 1

/-- Naturality of the actual connecting maps computes each edge coordinate. -/
theorem thetaCharacterCollapse_coordinates_of_connecting
    (z : SingularHomology (CompactFibreTorus × Theta) 2)
    (v : Fin 3 → SingularHomology CompactFibreTorus 1)
    (hz : thetaConnecting z = thetaBeltSum v) :
    threeCircleSuspensionHomologyTwoEquiv
        (singularHomologyMap thetaCharacterCollapse 2 z) =
      fun j => unitCircleHomologyOneEquiv
        (singularHomologyMap (thetaEdgeCharacterMap j) 1 (v j)) := by
  have hn := connectingHomomorphism_naturality_apply thetaCharacterCollapse
    thetaNorth thetaSouth Suspension.northOpen Suspension.southOpen
    thetaCharacterCollapse_mapsTo_north thetaCharacterCollapse_mapsTo_south
    thetaNorth_isOpen thetaSouth_isOpen theta_open_cover
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover 1 z
  change singularHomologyMap thetaBeltMap 1 (thetaConnecting z) = _ at hn
  rw [hz] at hn
  change thetaTargetBeltHomologyEquiv
    (connectingHomomorphism
      (Suspension.northOpen : Set ThreeCircleSuspension) Suspension.southOpen
      Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover 1
      (singularHomologyMap thetaCharacterCollapse 2 z)) = _
  rw [← hn]
  exact thetaBeltMap_homologyOne_sum v

/-- Every zero-sum triple has a preimage under the genuine connecting map. -/
theorem exists_thetaConnecting_eq_thetaBeltSum
    (v : Fin 3 → SingularHomology CompactFibreTorus 1) (hv : ∑ j, v j = 0) :
    ∃ z : SingularHomology (CompactFibreTorus × Theta) 2,
      thetaConnecting z = thetaBeltSum v := by
  have h : thetaBeltSum v ∈ LinearMap.range thetaConnecting := by
    rw [thetaConnecting, exact_at_intersection]
    exact thetaBeltSum_mem_ker v hv
  exact h

/-- The integral weight multiplies the determinant of the actual edge and phase vector. -/
theorem thetaEdgeCharacter_weighted_coordinateHomology
    (m : Fin 3 → ℤ) (w : Fin 2 → ℤ) (j : Fin 3) :
    unitCircleHomologyOneEquiv
        (singularHomologyMap (thetaEdgeCharacterMap j) 1
          (m j • compactPhaseCoordinateHomology w)) =
      m j * (hexagonRay (thetaEdgeIndex j) 0 * w 1 -
        hexagonRay (thetaEdgeIndex j) 1 * w 0) := by
  simp only [map_zsmul, zsmul_eq_mul, Int.cast_id]
  change m j * unitCircleHomologyOneEquiv
    (singularHomologyMap (edgeCharacterMap (hexagonRay (thetaEdgeIndex j))) 1
      (compactPhaseCoordinateHomology w)) = _
  rw [edgeCharacter_coordinateHomology]
  ring

/-- Zero-sum edge weights give zero-sum copies of any fixed phase class. -/
theorem sum_weighted_phaseHomology_eq_zero (m : Fin 3 → ℤ)
    (a : SingularHomology CompactFibreTorus 1) (hm : ∑ j, m j = 0) :
    (∑ j, m j • a) = 0 := by
  have h : (∑ j, m j • a) = (∑ j, m j) • a := by
    simp [Fin.sum_univ_succ, add_zsmul]
  rw [h, hm, zero_zsmul]

/-- Actual theta-product classes with the specified weighted phase connecting image. -/
theorem exists_thetaConnecting_eq_weighted_thetaBeltSum
    (m : Fin 3 → ℤ) (w : Fin 2 → ℤ) (hm : ∑ j, m j = 0) :
    ∃ z : SingularHomology (CompactFibreTorus × Theta) 2,
      thetaConnecting z = thetaBeltSum (fun j => m j • compactPhaseCoordinateHomology w) :=
  exists_thetaConnecting_eq_thetaBeltSum _
    (sum_weighted_phaseHomology_eq_zero m (compactPhaseCoordinateHomology w) hm)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- The actual boundary homeomorphism preserves the suspension's oriented marking. -/
theorem centralBoundaryHomologyTwo_doubleSuspensionBoundaryMap
    (a : SingularHomology ThreeCircleSuspension 2) :
    centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR
        (singularHomologyMap (doubleSuspensionBoundaryContinuousMap C r hr) 2 a) =
      threeCircleSuspensionHomologyTwoEquiv a := by
  change threeCircleSuspensionHomologyTwoEquiv
    ((homeomorphHomologyEquiv
      (doubleSuspensionBoundaryHomeomorph C r hr hr1 hC hR) 2).symm
      ((homeomorphHomologyEquiv
        (doubleSuspensionBoundaryHomeomorph C r hr hr1 hC hR) 2) a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Every boundary class is the indicated sum of actual oriented curve classes. -/
theorem centralBoundaryHomologyTwo_expansion
    (b : SingularHomology (centralBoundary C r hr) 2) :
    b = ∑ j : Fin 3, (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR b j) •
      centralDoubleCurveFundamentalClass C r hr hr1 hC hR j := by
  apply (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR).injective
  simp only [map_sum, map_zsmul, centralDoubleCurveFundamentalClass_coordinate]
  ext k
  simp [Pi.single_apply]

/-- The same expansion after the literal inclusion of the double locus. -/
theorem boundaryH2Inclusion_expansion
    (b : SingularHomology (centralBoundary C r hr) 2) :
    boundaryH2Inclusion C r hr b =
      ∑ j : Fin 3, (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR b j) •
        centralDoubleCurveH2Class C r hr hr1 hC hR j := by
  conv_lhs => rw [centralBoundaryHomologyTwo_expansion C r hr hr1 hC hR b]
  simp only [map_sum, map_zsmul, centralDoubleCurveH2Class]

/-- Specialization of any actual theta-product class, read from its actual
Mayer--Vietoris connecting image, in the three named central double curves. -/
theorem productCollapse_thetaProductMap_of_connecting
    (z : SingularHomology (CompactFibreTorus × Theta) 2)
    (v : Fin 3 → SingularHomology CompactFibreTorus 1)
    (hz : thetaConnecting z = thetaBeltSum v) :
    singularHomologyMap (productCollapse C r hr) 2
        (singularHomologyMap thetaProductMap 2 z) =
      ∑ j : Fin 3, (unitCircleHomologyOneEquiv
        (singularHomologyMap (thetaEdgeCharacterMap j) 1 (v j))) •
          centralDoubleCurveH2Class C r hr hr1 hC hR j := by
  have h := congrArg (fun f => singularHomologyMap f 2)
    (centralBoundaryInclusion_comp_boundaryLift C r hr)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  have he := LinearMap.congr_fun h z
  change singularHomologyMap (centralBoundaryInclusion C r hr) 2
      (singularHomologyMap (boundaryLift C r hr) 2 z) =
    singularHomologyMap (productCollapse C r hr) 2
      (singularHomologyMap thetaProductMap 2 z) at he
  rw [← he, boundaryLift_homology_eq, LinearMap.comp_apply]
  change boundaryH2Inclusion C r hr
    (singularHomologyMap (doubleSuspensionBoundaryContinuousMap C r hr) 2
      (singularHomologyMap thetaCharacterCollapse 2 z)) = _
  rw [boundaryH2Inclusion_expansion C r hr hr1 hC hR,
    centralBoundaryHomologyTwo_doubleSuspensionBoundaryMap C r hr hr1 hC hR,
    thetaCharacterCollapse_coordinates_of_connecting z v hz]

/-- On a weighted coordinate phase class the actual coefficient is the
oriented edge determinant, multiplied by the corresponding edge weight. -/
theorem productCollapse_thetaProductMap_of_coordinate_connecting
    (z : SingularHomology (CompactFibreTorus × Theta) 2)
    (m : Fin 3 → ℤ) (w : Fin 2 → ℤ)
    (hz : thetaConnecting z =
      thetaBeltSum (fun j => m j • compactPhaseCoordinateHomology w)) :
    singularHomologyMap (productCollapse C r hr) 2
        (singularHomologyMap thetaProductMap 2 z) =
      ∑ j : Fin 3, (m j * (hexagonRay (thetaEdgeIndex j) 0 * w 1 -
        hexagonRay (thetaEdgeIndex j) 1 * w 0)) •
          centralDoubleCurveH2Class C r hr hr1 hC hR j := by
  rw [productCollapse_thetaProductMap_of_connecting C r hr hr1 hC hR z _ hz]
  simp only [thetaEdgeCharacter_weighted_coordinateHomology]

/-- Zero-sum edge weights produce a genuine source class with both the specified
connecting image and the proved geometric specialization formula. -/
theorem exists_productCollapse_thetaProductMap_coordinate
    (m : Fin 3 → ℤ) (w : Fin 2 → ℤ) (hm : ∑ j, m j = 0) :
    ∃ z : SingularHomology (CompactFibreTorus × Theta) 2,
      thetaConnecting z = thetaBeltSum (fun j => m j • compactPhaseCoordinateHomology w) ∧
      singularHomologyMap (productCollapse C r hr) 2
          (singularHomologyMap thetaProductMap 2 z) =
        ∑ j : Fin 3, (m j * (hexagonRay (thetaEdgeIndex j) 0 * w 1 -
          hexagonRay (thetaEdgeIndex j) 1 * w 0)) •
            centralDoubleCurveH2Class C r hr hr1 hC hR j := by
  obtain ⟨z, hz⟩ := exists_thetaConnecting_eq_weighted_thetaBeltSum m w hm
  exact ⟨z, hz,
    productCollapse_thetaProductMap_of_coordinate_connecting C r hr hr1 hC hR z m w hz⟩

end Wikipedia.HopfProblem.CuspCentralHomology
