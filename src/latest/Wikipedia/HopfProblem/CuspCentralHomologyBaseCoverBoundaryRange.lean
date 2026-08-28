import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverRadius
import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusTheta

/-!
# The theta map covers exactly the actual base boundary

The six straight sides cover the literal frontier of the fundamental
hexagon. Opposite sides differ by the proved integral translation, with
reversed interval parameter. Thus the three chosen oriented sides cover
precisely the radius-one subset of the actual marked base torus.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open CuspHoneycombTiling ToricComponent

local notation "Plane" => CuspHoneycombTiling.Plane

theorem dualSidePoint_mem_frontier (k : Fin 6) (t : unitInterval) :
    dualSidePoint k t ∈ frontier baseCell := by
  rw [← edgeArcBase_eq_dualSidePoint (0 : Matrix (Fin 2) (Fin 2) ℂ)]
  exact edgeArcBase_mem_frontier 0 k t

theorem exists_dualSidePoint_of_mem_frontier (y : Plane) (hy : y ∈ frontier baseCell) :
    ∃ k : Fin 6, ∃ t : unitInterval, dualSidePoint k t = y := by
  obtain ⟨k, t, ht⟩ := exists_edgeArcBase_of_mem_frontier
    (0 : Matrix (Fin 2) (Fin 2) ℂ) y hy
  exact ⟨k, t, (edgeArcBase_eq_dualSidePoint 0 k t).symm.trans ht⟩

/-- Opposite sides have exactly the integral displacement of their
common neighboring cell, including both endpoints. -/
theorem dualSidePoint_opposite (k : Fin 6) (t : unitInterval) :
    dualSidePoint (k + 3) (unitInterval.symm t) =
      dualSidePoint k t - latticePoint (hexagonRay k) :=
  dual_sideInterval_opposite k t

theorem basePoint_dualSidePoint_opposite (k : Fin 6) (t : unitInterval) :
    baseTorusPoint (dualSidePoint (k + 3) (unitInterval.symm t)) =
      baseTorusPoint (dualSidePoint k t) := by
  rw [dualSidePoint_opposite]
  exact basePoint_sub_latticePoint (hexagonRay k) (dualSidePoint k t)

theorem thetaBaseMap_mem_boundary (q : Theta) : thetaBaseMap q ∈ boundary := by
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [thetaBaseMap_mk_point]
  let y := dualSidePoint (thetaEdgeIndex j) (if j = 1 then unitInterval.symm t else t)
  have hy : y ∈ frontier baseCell := dualSidePoint_mem_frontier _ _
  exact (cellMap_mem_boundary_iff ⟨y, baseCell_isClosed.frontier_subset hy⟩).mpr hy

/-- Each original side is represented by one of the three actual theta
edges, with the existing orientation convention. -/
theorem dualSidePoint_basePoint_mem_range (k : Fin 6) (t : unitInterval) :
    baseTorusPoint (dualSidePoint k t) ∈ range thetaBaseMap := by
  fin_cases k
  · exact ⟨Suspension.mk t (0 : Fin 3), thetaBaseMap_mk_zero t⟩
  · refine ⟨Suspension.mk (unitInterval.symm t) (1 : Fin 3), ?_⟩
    rw [thetaBaseMap_mk_one, unitInterval.symm_symm]
    rfl
  · exact ⟨Suspension.mk t (2 : Fin 3), thetaBaseMap_mk_two t⟩
  · refine ⟨Suspension.mk (unitInterval.symm t) (0 : Fin 3), ?_⟩
    rw [thetaBaseMap_mk_zero]
    have hi : (0 : Fin 6) + 3 = ⟨3, by decide⟩ := by decide
    simpa only [unitInterval.symm_symm, hi] using
      (basePoint_dualSidePoint_opposite 0 (unitInterval.symm t)).symm
  · refine ⟨Suspension.mk t (1 : Fin 3), ?_⟩
    rw [thetaBaseMap_mk_one]
    have hi : (1 : Fin 6) + 3 = ⟨4, by decide⟩ := by decide
    simpa only [unitInterval.symm_symm, hi] using
      (basePoint_dualSidePoint_opposite 1 (unitInterval.symm t)).symm
  · refine ⟨Suspension.mk (unitInterval.symm t) (2 : Fin 3), ?_⟩
    rw [thetaBaseMap_mk_two]
    have hi : (2 : Fin 6) + 3 = ⟨5, by decide⟩ := by decide
    simpa only [unitInterval.symm_symm, hi] using
      (basePoint_dualSidePoint_opposite 2 (unitInterval.symm t)).symm

/-- This is equality with the actual radius-one locus in `ProductTorus 2`,
not the boundary of an abstract cell complex. -/
theorem range_thetaBaseMap : range thetaBaseMap = boundary := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact thetaBaseMap_mem_boundary x
  · intro hq
    obtain ⟨y, rfl⟩ := cellMap_surjective q
    obtain ⟨k, t, ht⟩ := exists_dualSidePoint_of_mem_frontier
      (y : Plane) ((cellMap_mem_boundary_iff y).mp hq)
    change baseTorusPoint (y : Plane) ∈ range thetaBaseMap
    rw [← ht]
    exact dualSidePoint_basePoint_mem_range k t

/-- The actual theta map with codomain restricted to its exact boundary image. -/
def thetaBoundaryMap : C(Theta, boundary) :=
  ⟨fun q => ⟨thetaBaseMap q, thetaBaseMap_mem_boundary q⟩,
    thetaBaseMap.continuous.subtype_mk _⟩

@[simp] theorem thetaBoundaryMap_coe (q : Theta) :
    (thetaBoundaryMap q : BaseTorus) = thetaBaseMap q := rfl

theorem thetaBoundaryMap_surjective : Function.Surjective thetaBoundaryMap := by
  intro q
  have hq : (q : BaseTorus) ∈ range thetaBaseMap := range_thetaBaseMap.symm.le q.2
  obtain ⟨x, hx⟩ := hq
  exact ⟨x, Subtype.ext hx⟩

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover
