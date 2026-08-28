import Wikipedia.NoExoticSixSphere.RoundedTraceCollapseHomotopy
import Wikipedia.NoExoticSixSphere.RoundedTraceVerticalBoundaryFrame
import Wikipedia.NoExoticSixSphere.OpenProductSlice

/-!
# Exact endpoint tubes and their collapse maps

Restrict the actual compactified cylinder tube to either exact end. The
spatial endpoint tube is an open embedding, and its one-point collapse is
exactly the corresponding endpoint of the constructed homotopy. Its formula
uses the actual spatial boundary frame, not just the same zero fiber.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def tubeEndBase (top : Bool) : Set (ambientSet A) := if top then topEnd A else otherEnd A

def tubeEndBoundaryPoint (top : Bool) (p : tubeEndBase A top) : Boundary A := by
  let := traceChartedSpace A
  refine ⟨p.val, (boundary_iff_mem_ends A p.val).mpr ?_⟩
  cases top
  · exact Or.inl p.property
  · exact Or.inr p.property

namespace SlabTubeData

variable {A} (D : SlabTubeData A)

theorem compactCylinderTube_end_iff (top : Bool) (p : ambientSet A)
    (v : TimeGraphFrameSpace (e := e)) :
    (D.compactCylinderTube (p, v)).1 = (if top then 1 else 0 : I) ↔ p ∈ tubeEndBase A top := by
  cases top
  · rw [Subtype.ext_iff]
    change timeGraphTimeFunctional (e := e) (D.openTube (p, v)).val = 0 ↔ p ∈ otherEnd A
    exact D.openTube_other_end p v
  · rw [Subtype.ext_iff]
    change timeGraphTimeFunctional (e := e) (D.openTube (p, v)).val = 1 ↔ p ∈ topEnd A
    exact D.openTube_top_end p v

def endTube (top : Bool) (q : tubeEndBase A top × TimeGraphFrameSpace (e := e)) :
    Vector (e.ambientDimension + 6) :=
  (timeGraphCoordinates (e := e) (D.openTube (q.1.val, q.2)).val).2

def compactEndTube (top : Bool) : tubeEndBase A top × TimeGraphFrameSpace (e := e) →
    OnePoint (Vector (e.ambientDimension + 6)) :=
  OpenProductSlice.slice D.compactCylinderTube (tubeEndBase A top)

theorem compactEndTube_apply (top : Bool)
    (q : tubeEndBase A top × TimeGraphFrameSpace (e := e)) :
    D.compactEndTube top q = (D.endTube top q : OnePoint _) := rfl

theorem isOpenEmbedding_compactEndTube (top : Bool) : IsOpenEmbedding (D.compactEndTube top) :=
  OpenProductSlice.isOpenEmbedding_slice (D.compactCylinderTube_end_iff top)
    D.isOpenEmbedding_compactCylinderTube

theorem isOpenEmbedding_endTube (top : Bool) : IsOpenEmbedding (D.endTube top) :=
  IsOpenEmbedding.of_comp (D.endTube top) OnePoint.isOpenEmbedding_coe
    (D.isOpenEmbedding_compactEndTube top)

theorem endTube_core (top : Bool) (p : tubeEndBase A top) :
    D.endTube top (p, 0) = p.val.val := by
  rw [endTube, D.openTube_core, timeGraph_coordinates]

theorem endTube_apply (top : Bool) (q : tubeEndBase A top × TimeGraphFrameSpace (e := e)) :
    D.endTube top q = q.1.val.val + boundaryVerticalFrame A (tubeEndBoundaryPoint A top q.1)
      (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e)) D.radius q.2) := by
  change (timeGraphCoordinates (e := e)
    (timeGraph A q.1.val + verticalFrame A q.1.val
      (OpenPartialHomeomorph.univBall (0 : TimeGraphFrameSpace (e := e)) D.radius q.2))).2 = _
  rw [map_add, timeGraph_coordinates]
  rfl

theorem endCollapse_eq_onePoint_endTube (top : Bool)
    (z : OnePoint (Vector (e.ambientDimension + 6))) :
    D.endCollapse (if top then 1 else 0) z =
      OpenFiberCollapse.collapseOnePoint (D.endTube top) z :=
  OpenProductSlice.collapse_slice (D.compactCylinderTube_end_iff top)
    D.isOpenEmbedding_compactCylinderTube.injective z

end SlabTubeData

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
