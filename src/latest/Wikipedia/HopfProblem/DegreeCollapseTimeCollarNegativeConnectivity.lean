import Wikipedia.HopfProblem.DegreeCollapseOpenCoverConnectedPart
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarOverlap
import Wikipedia.HopfProblem.DegreeCollapseTrivialPatchVanKampen

/-!
# Simple connectivity of the original complementary half

The actual overlap retracts onto the boundary. Ambient connectedness and
local path connectedness first give path connectedness of the negative
open half. The proved van Kampen inverse for adding a simply connected
patch then detects simple connectivity of that original open half.
The collar homotopy equivalence transfers it to the closed half.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open FundamentalGroupVanKampen

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [LocallyPathConnectedSpace M] [SimplyConnectedSpace M] [SimplyConnectedSpace B]
  {t : M → ℝ} (C : TimeCollar t B) [SimplyConnectedSpace (NonnegativeHalf t)]

theorem negativeOpen_simplyConnected : SimplyConnectedSpace C.reverse.positiveOpen := by
  let : SimplyConnectedSpace C.positiveOpen := C.positiveHalfHomotopyEquiv.simplyConnectedSpace
  let : SimplyConnectedSpace C.overlap := C.overlapHomotopyEquiv.simplyConnectedSpace
  have hI : IsPathConnected C.overlap := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  let : PathConnectedSpace C.reverse.positiveOpen :=
    OpenCoverConnectivity.right_pathConnected C.positiveOpen.isOpen C.reverse.positiveOpen.isOpen
      C.open_halves_cover hI
  let o : C.overlap := Classical.choice inferInstance
  let D : TwoOpenCover M := {
    U := C.reverse.positiveOpen
    V := C.positiveOpen
    cover := by rw [union_comm]; exact C.open_halves_cover
    pathConnectedU := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
    pathConnectedV := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
    pathConnectedIntersection := by rw [inter_comm]; exact hI
    base := o.val
    baseU := o.property.2
    baseV := o.property.1 }
  let : SimplyConnectedSpace D.V := inferInstanceAs (SimplyConnectedSpace C.positiveOpen)
  let e : D.overlap ≃ₜ C.overlap := Homeomorph.setCongr
    (inter_comm (C.reverse.positiveOpen : Set M) (C.positiveOpen : Set M))
  let : SimplyConnectedSpace D.overlap := e.toHomotopyEquiv.simplyConnectedSpace
  exact (AttachmentConnectivity.simplyConnected_iff_old D).mp inferInstance

include C in
theorem negativeHalf_simplyConnected :
    SimplyConnectedSpace (NonnegativeHalf (fun p : M ↦ -t p)) := by
  let : SimplyConnectedSpace C.reverse.positiveOpen := C.negativeOpen_simplyConnected
  exact C.reverse.positiveHalfHomotopyEquiv.symm.simplyConnectedSpace

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
