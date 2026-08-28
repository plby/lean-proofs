import Wikipedia.HopfProblem.DegreeCollapseTrivialPatchVanKampen
import Wikipedia.HopfProblem.DegreeCollapseCellComponentCriterion
import Wikipedia.SmoothSixDPoincare.CellCoverHomotopy

/-!
# An actual cell with simply connected attaching sphere preserves simple connectivity

The real open cell cover has a contractible disk patch and an annular
overlap homotopy equivalent to the attaching sphere. Van Kampen therefore
preserves the old fundamental group. In the reverse direction the already
proved degree-zero component criterion supplies old path connectedness;
it is not assumed from connectedness of the ambient attachment.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.AttachmentConnectivity

open Wikipedia.SmoothSixDPoincare FundamentalGroupVanKampen MorseCancellation

variable {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
  (D : EmbeddedCellAttachment N X)

def cellCover [PathConnectedSpace D.old] [PathConnectedSpace (sphere (0 : N) 1)] :
    TwoOpenCover X := by
  let : PathConnectedSpace D.oldNeighborhood :=
    pathConnectedSpace_of_homotopyEquiv D.oldHomotopyEquiv.symm
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let : PathConnectedSpace ↥(D.oldNeighborhood ∩ D.diskPatch) :=
    pathConnectedSpace_of_homotopyEquiv D.overlapSphereEquiv.symm
  let z : ↥(D.oldNeighborhood ∩ D.diskPatch) := Classical.arbitrary _
  exact {
    U := ⟨D.oldNeighborhood, D.isOpen_oldNeighborhood⟩
    V := ⟨D.diskPatch, D.isOpen_diskPatch⟩
    cover := D.open_cover
    pathConnectedU := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
    pathConnectedV := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
    pathConnectedIntersection := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
    base := z.val
    baseU := z.property.1
    baseV := z.property.2 }

theorem cell_simplyConnected_iff_of_old_pathConnected
    [PathConnectedSpace D.old] [SimplyConnectedSpace (sphere (0 : N) 1)] :
    SimplyConnectedSpace X ↔ SimplyConnectedSpace D.old := by
  let C := cellCover D
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let : SimplyConnectedSpace C.V := inferInstanceAs (SimplyConnectedSpace D.diskPatch)
  let : SimplyConnectedSpace C.overlap := D.overlapSphereEquiv.symm.simplyConnectedSpace
  have h := simplyConnected_iff_old C
  change SimplyConnectedSpace X ↔ SimplyConnectedSpace D.oldNeighborhood at h
  exact h.trans D.oldHomotopyEquiv.simplyConnectedSpace_iff.symm

theorem cell_simplyConnected_iff [SimplyConnectedSpace (sphere (0 : N) 1)] :
    SimplyConnectedSpace X ↔ SimplyConnectedSpace D.old := by
  constructor
  · intro h
    let : SimplyConnectedSpace X := h
    let s : sphere (0 : N) 1 := Classical.arbitrary _
    let : PathConnectedSpace D.old :=
      cell_old_pathConnected_of_attaching_component D (D.attachingSphere s)
        (fun u ↦ (PathConnectedSpace.joined u s).map D.attachingSphere.continuous)
    exact (cell_simplyConnected_iff_of_old_pathConnected D).mp h
  · intro h
    let : SimplyConnectedSpace D.old := h
    exact (cell_simplyConnected_iff_of_old_pathConnected D).mpr h

end Wikipedia.HopfProblem.DegreeCollapse.AttachmentConnectivity
