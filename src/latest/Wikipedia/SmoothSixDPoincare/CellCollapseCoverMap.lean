import Wikipedia.SmoothSixDPoincare.AttachmentOnePointCollapse
import Wikipedia.SmoothSixDPoincare.CellCoverHomotopy
import Wikipedia.SmoothSixDPoincare.OnePointCollapseCover
import Wikipedia.SmoothSixDPoincare.CoverConnectingNaturality

/-!
# The actual cell collapse is a map of the constructed open covers

The old neighborhood avoids the cell center, and the disk patch avoids the
old space. Thus the original collapse carries these pieces into the two
punctured compactification charts. The overlap sphere has an exact radial
formula, retaining the radius-three-quarters source parametrization.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare

namespace OnePointCover

def overlapRadius : ℝ := (Real.sqrt (1 - (3 / 4 : ℝ) ^ 2))⁻¹ * (3 / 4)

theorem overlapRadius_pos : 0 < overlapRadius := by
  have h : 0 < 1 - (3 / 4 : ℝ) ^ 2 := by norm_num
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr h)) (by norm_num)

end OnePointCover

namespace EmbeddedCellAttachment

variable {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X)

theorem collapseMap_eq_zero_iff (x : X) :
    D.collapseMap x = ((0 : N) : OnePoint N) ↔ D.cell ⟨0, by simp⟩ = x := by
  have hx : x ∈ D.old ∪ range D.cell := by rw [D.cover]; trivial
  rcases hx with hx | ⟨z, rfl⟩
  · rw [D.collapseMap_old ⟨x, hx⟩]
    constructor
    · intro h
      exact (OnePoint.infty_ne_coe (0 : N) h).elim
    · intro h
      rw [← h, D.boundary] at hx
      simp at hx
  · rw [D.collapseMap_cell, DiskOnePointCollapse.collapse_eq_zero_iff]
    constructor
    · intro hz
      exact congrArg D.cell (Subtype.ext hz.symm)
    · intro hz
      exact (congrArg Subtype.val (D.cell_closed.injective hz)).symm

theorem collapseMaps_oldNeighborhood :
    MapsTo D.collapseMap D.oldNeighborhood (OnePointCover.oldPatch (N := N)) := by
  intro x hx
  change D.collapseMap x ≠ ((0 : N) : OnePoint N)
  intro h
  have heq := (D.collapseMap_eq_zero_iff x).mp h
  rw [← heq, D.cell_mem_oldNeighborhood_iff] at hx
  norm_num at hx

theorem collapseMaps_diskPatch :
    MapsTo D.collapseMap D.diskPatch (OnePointCover.finitePatch (N := N)) := by
  intro x hx
  change D.collapseMap x ≠ OnePoint.infty
  exact fun h => hx ((D.collapseMap_infty_iff x).mp h)

def collapseOverlapMap : C(↥(D.oldNeighborhood ∩ D.diskPatch),
    ↥(OnePointCover.oldPatch (N := N) ∩ OnePointCover.finitePatch)) :=
  CoverNaturality.mapOn D.collapseMap _ _
    (CoverNaturality.map_intersection _ _ _ _ D.collapseMap
      D.collapseMaps_oldNeighborhood D.collapseMaps_diskPatch)

/-- The literal overlap map, including its positive radial scale. -/
theorem collapseOverlap_sphere (u : sphere (0 : N) 1) :
    D.collapseOverlapMap (D.overlapSphereEquiv u) =
      OnePointCover.overlapSphereEquiv OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos u := by
  apply Subtype.ext
  change D.collapseMap (D.cell (DiskAnnulus.middleDisk u)) =
    ((OnePointCover.overlapRadius • (u : N) : N) : OnePoint N)
  rw [D.collapseMap_cell, DiskOnePointCollapse.collapse_interior _
    (DiskAnnulus.middleDisk_mem u).2]
  apply congrArg (OnePoint.some : N → OnePoint N)
  change (Real.sqrt (1 - ‖(3 / 4 : ℝ) • (u : N)‖ ^ 2))⁻¹ •
    ((3 / 4 : ℝ) • (u : N)) = OnePointCover.overlapRadius • (u : N)
  rw [DiskAnnulus.norm_middle, smul_smul]
  rfl

theorem collapseOverlap_comp_sphere :
    D.collapseOverlapMap.comp D.overlapSphereEquiv.toFun =
      (OnePointCover.overlapSphereEquiv (N := N) OnePointCover.overlapRadius
        OnePointCover.overlapRadius_pos).toFun :=
  ContinuousMap.ext D.collapseOverlap_sphere

end EmbeddedCellAttachment
end Wikipedia.SmoothSixDPoincare
