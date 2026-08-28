import Wikipedia.HopfProblem.DegreeCollapseCellSimpleConnectivity
import Wikipedia.HopfProblem.DegreeCollapseSurgerySecondHomology
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# Actual framed surgery preserves simple connectedness

The original cylinder has the original manifold's homotopy type. The
four-cell presentation therefore makes the actual trace simply connected.
Viewed from its other end, that same trace is a three-cell attachment;
the reverse implication of cell simple connectivity applies. Transport
through the retained native boundary homeomorphism gives simple
connectedness of the canonical surgery target itself.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

include hR in
theorem trace_simplyConnected : SimplyConnectedSpace (ambientSet A) := by
  let D := TraceCoreAttachment.corePresentation A hR
  let E : M ≃ₕ D.old := (TraceCoreAttachment.topCylinderHomotopyEquiv A).trans
    (TraceCoreAttachment.cylinderOldHomeomorph A hR).toHomotopyEquiv
  let : SimplyConnectedSpace D.old := E.symm.simplyConnectedSpace
  let : SimplyConnectedSpace (sphere (0 : Vector 4) 1) := EuclideanSphere.simplyConnectedSpace 1
  let : SimplyConnectedSpace
      ↥(range (UnroundedTrace.cylinderMap A) ∪ range (TraceCoreAttachment.coreCellMap A)) :=
    (AttachmentConnectivity.cell_simplyConnected_iff D).mpr inferInstance
  exact (TraceCoreAttachment.coreUnionTraceHomotopyEquiv A hR).symm.simplyConnectedSpace

theorem nativeTarget_simplyConnected : SimplyConnectedSpace (UnitSurgery.Target A hR) := by
  let : SimplyConnectedSpace (ambientSet A) := trace_simplyConnected A hR
  let : SimplyConnectedSpace ↥(flatBoundarySet A hR ∪ range (reverseCoreMap A hR)) :=
    (reverseCoreUnionTraceHomotopyEquiv A hR).simplyConnectedSpace
  let : SimplyConnectedSpace (sphere (0 : Vector 3) 1) := EuclideanSphere.simplyConnectedSpace 0
  let : SimplyConnectedSpace (reverseCorePresentation A hR).old :=
    (AttachmentConnectivity.cell_simplyConnected_iff
      (reverseCorePresentation A hR)).mp inferInstance
  exact (nativeOldHomeomorph A hR).toHomotopyEquiv.simplyConnectedSpace

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
