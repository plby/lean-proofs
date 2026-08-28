import Wikipedia.HopfProblem.DegreeCollapseEmbeddedHandleCell
import Wikipedia.HopfProblem.DegreeCollapseCellSimpleConnectivity

/-!
# Simple connectivity through the actual whole-handle attachment

The constructed core-cell homotopy equivalence and original old-space
homeomorphism transport the cell theorem in both directions. The actual
attaching sphere, rather than a dimension-only substitute, supplies the
simple-connectivity hypothesis.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.EmbeddedHandle

open Wikipedia.SmoothSixDPoincare PuncturedHandle MorseHandle

variable {N P R X : Type}
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace R] [TopologicalSpace X] [T2Space X]
  (D : EmbeddedHandle N P R X)

include D in
theorem simplyConnected_iff [SimplyConnectedSpace (UnitSphere N)] :
    SimplyConnectedSpace X ↔ SimplyConnectedSpace R :=
  D.coreHomotopyEquiv.simplyConnectedSpace_iff.symm.trans
    ((AttachmentConnectivity.cell_simplyConnected_iff D.corePresentation).trans
      D.oldHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.symm)

end Wikipedia.HopfProblem.DegreeCollapse.EmbeddedHandle
