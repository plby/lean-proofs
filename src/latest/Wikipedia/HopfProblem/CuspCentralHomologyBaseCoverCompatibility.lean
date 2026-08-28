import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverBoundary
import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverCollar
import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverOverlap

/-!
# The actual base-cover attaching maps

The outward collar retraction on the actual overlap is exactly its
radial direction followed by the original frontier quotient. In theta
coordinates this is the actual hexagonal attaching map, not an assumed
cellular boundary. Radial contraction inside the closed hexagon also
provides an explicit nullhomotopy after inclusion into the base torus.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

/-- The circle coordinate of the overlap is exactly the radial circle
coordinate of its actual normalized frontier direction. -/
theorem overlapCircleHomotopyEquiv_eq_direction (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (q : overlapRegion a) :
    overlapCircleHomotopyEquiv a ha ha1 q =
      Radial.frontierCellCircleHomeomorph (overlapDirection a ha q) := rfl

/-- The original overlap inclusion, followed by the genuine collar
retraction, is precisely the actual frontier attaching map. -/
theorem overlapIntoOuter_boundary_map (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (outerRegionRetraction a ha ha1).comp (overlapIntoOuter a) =
      circleBoundaryMap.comp (overlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨y, rfl⟩ := (annulusOverlapHomeomorph a).surjective q
  apply Subtype.ext
  have hin : overlapIntoOuter a (annulusOverlapHomeomorph a y) =
      collarCellMap a ⟨(y : Plane), y.2.1, y.2.2.le⟩ := rfl
  change (outerRegionRetraction a ha ha1
      (overlapIntoOuter a (annulusOverlapHomeomorph a y)) : BaseTorus) =
    (circleBoundaryMap
      (overlapCircleHomotopyEquiv a ha ha1 (annulusOverlapHomeomorph a y)) : BaseTorus)
  rw [hin, outerRegionRetraction_collarCellMap, circleBoundaryMap_coe,
    overlapCircleHomotopyEquiv_eq_direction, Homeomorph.symm_apply_apply,
    overlapDirection_annulus]

/-- The actual outer open subset has the homotopy type of the literal
three-edge theta graph, through its boundary-fixed radial deformation. -/
def outerRegionThetaHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    outerRegion a ≃ₕ Theta :=
  (outerRegionBoundaryHomotopyEquiv a ha ha1).trans
    boundaryThetaHomeomorph.toHomotopyEquiv

@[simp] theorem outerRegionThetaHomotopyEquiv_apply
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (q : outerRegion a) :
    outerRegionThetaHomotopyEquiv a ha ha1 q =
      boundaryThetaHomeomorph (outerRegionRetraction a ha ha1 q) := rfl

@[simp] theorem outerRegionThetaHomotopyEquiv_symm_apply
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (q : Theta) :
    (outerRegionThetaHomotopyEquiv a ha ha1).symm q =
      outerRegionBoundaryInclusion a ha1 (boundaryThetaHomeomorph.symm q) := rfl

/-- Exact compatibility of the actual base-cover map with the constructed
theta and circle coordinates. -/
theorem overlapIntoOuter_theta_map (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (outerRegionThetaHomotopyEquiv a ha ha1).toFun.comp (overlapIntoOuter a) =
      circleThetaMap.comp (overlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro q
  exact congrArg (fun f : C(overlapRegion a, boundary) => boundaryThetaHomeomorph (f q))
    (overlapIntoOuter_boundary_map a ha ha1)

/-- After inclusion in the actual base torus, the hexagonal attaching
loop contracts by radial scaling in the original closed cell. -/
def baseBoundaryNullhomotopy :
    (boundaryInclusion.comp circleBoundaryMap).Homotopy
      (ContinuousMap.const Circle (baseTorusPoint (0 : Plane))) where
  toFun p := baseTorusPoint ((1 - (p.1 : ℝ)) •
    (Radial.frontierCellCircleHomeomorph.symm p.2 : Plane))
  continuous_toFun := baseTorusPoint_continuous.comp
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp
        (Radial.frontierCellCircleHomeomorph.symm.continuous.comp continuous_snd)))
  map_zero_left z := by
    change baseTorusPoint ((1 - (0 : ℝ)) •
      (Radial.frontierCellCircleHomeomorph.symm z : Plane)) = _
    rw [sub_zero, one_smul]
    rfl
  map_one_left z := by
    change baseTorusPoint ((1 - (1 : ℝ)) •
      (Radial.frontierCellCircleHomeomorph.symm z : Plane)) = _
    rw [sub_self, zero_smul]
    rfl

theorem baseBoundary_homotopic_const :
    (boundaryInclusion.comp circleBoundaryMap).Homotopic
      (ContinuousMap.const Circle (baseTorusPoint (0 : Plane))) :=
  ⟨baseBoundaryNullhomotopy⟩

/-- The same explicit contraction with the actual theta attaching map
and actual theta inclusion in the statement. -/
theorem thetaBaseMap_circleThetaMap_homotopic_const :
    (thetaBaseMap.comp circleThetaMap).Homotopic
      (ContinuousMap.const Circle (baseTorusPoint (0 : Plane))) := by
  rw [thetaBaseMap_circleThetaMap]
  exact baseBoundary_homotopic_const

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover
