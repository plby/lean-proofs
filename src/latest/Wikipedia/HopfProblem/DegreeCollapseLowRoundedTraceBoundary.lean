import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceAtlas

/-!

# The exact native boundary of the globally charted rounded attachment

The boundary is the union of the remaining cylinder endpoints, transverse
handle sphere, and rounded zero level, each expressed in its actual open
piece coordinates. The gluing inclusions are local diffeomorphisms, so this
description is proved for the global manifold boundary.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel LowRoundedHandleCorner

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def pieceBoundary (i : Piece) : Set (pieceDomain A i) := by
  cases i with
  | cylinder =>
      exact {p | (unchangedCylinderHomeomorph A p).val.val.2 = 0 ∨
        (unchangedCylinderHomeomorph A p).val.val.2 = UnroundedTrace.height A}
  | handle =>
      exact {p | (unchangedHandleHomeomorph A p).val.val.2 ∈
        sphere (0 : Vector (7 - d)) (UnroundedTrace.handleRadius A)}
  | collar =>
      exact {p | collarLevel (bump A) (UnroundedTrace.handleRadius A)
        ((collarHomeomorph A).symm p).val = 0}

def traceBoundarySet : Set (ambientSet A) := ⋃ i, Subtype.val '' pieceBoundary A i

variable [IsManifold (𝓡 7) ∞ M]

theorem piece_isBoundaryPoint_iff (i : Piece) (p : pieceDomain A i) : letI := pieceAtlas A i;
    (ProductHalfSpace.model (Vector 7)).IsBoundaryPoint p ↔ p ∈ pieceBoundary A i := by
  cases i with
  | cylinder => exact unchangedCylinder_isBoundaryPoint_iff A p
  | handle => exact unchangedHandle_isBoundaryPoint_iff A p
  | collar => exact collar_isBoundaryPoint_iff A p

theorem trace_isBoundaryPoint_iff (p : ambientSet A) : letI := traceChartedSpace A;
    (ProductHalfSpace.model (Vector 7)).IsBoundaryPoint p ↔ p ∈ traceBoundarySet A := by
  let := traceChartedSpace A
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := pieceDomain_covers A p
    let := pieceAtlas A i
    let q : pieceDomain A i := ⟨p, hi⟩
    apply mem_iUnion.mpr
    refine ⟨i, q, ?_, rfl⟩
    exact (piece_isBoundaryPoint_iff A i q).mp
      (((openCover A).isBoundaryPoint_inclusion_iff i q).mpr hp)
  · intro hp
    obtain ⟨i, q, hq, he⟩ := mem_iUnion.mp hp
    let := pieceAtlas A i
    have hb := (piece_isBoundaryPoint_iff A i q).mpr hq
    have hg := ((openCover A).isBoundaryPoint_inclusion_iff i q).mp hb
    exact he ▸ hg

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

