import ErdosProblems.Erdos733.ST.PolygonalReplacementBoundaryPointData

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementEdgeBoundaryEndpointData]
structure PolygonalReplacementEdgeBoundaryEndpointData {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks) where
-- BODY
  edgeSourceVertex : G.edgeFinset → V
  edgeTargetVertex : G.edgeFinset → V
  edgeSourceVertex_mem : ∀ e, edgeSourceVertex e ∈ e.1
  edgeTargetVertex_mem : ∀ e, edgeTargetVertex e ∈ e.1
  edgeSource_eq_vertexPlacement :
    ∀ e, D.edgeSource e = D.vertexPlacement (edgeSourceVertex e)
  edgeTarget_eq_vertexPlacement :
    ∀ e, D.edgeTarget e = D.vertexPlacement (edgeTargetVertex e)
  sourceBoundaryIndex : G.edgeFinset → boundaryPoints.boundaryIndex
  targetBoundaryIndex : G.edgeFinset → boundaryPoints.boundaryIndex
  sourceBoundaryPoint : G.edgeFinset → EuclideanSpace ℝ (Fin 2)
  targetBoundaryPoint : G.edgeFinset → EuclideanSpace ℝ (Fin 2)
  sourceBoundaryPoint_eq :
    ∀ e, sourceBoundaryPoint e = boundaryPoints.point (sourceBoundaryIndex e)
  targetBoundaryPoint_eq :
    ∀ e, targetBoundaryPoint e = boundaryPoints.point (targetBoundaryIndex e)
  sourceBoundaryIndex_owner :
    ∀ e, boundaryPoints.owner (sourceBoundaryIndex e) = e
  targetBoundaryIndex_owner :
    ∀ e, boundaryPoints.owner (targetBoundaryIndex e) = e
  sourceBoundary_on_control_boundary :
    ∀ e,
      sourceBoundaryPoint e ∈
          Metric.sphere (D.vertexPlacement (edgeSourceVertex e))
            (controlDisks.vertexRadius (edgeSourceVertex e)) ∧
        sourceBoundaryPoint e ∈ D.edgeCarrier e
  targetBoundary_on_control_boundary :
    ∀ e,
      targetBoundaryPoint e ∈
          Metric.sphere (D.vertexPlacement (edgeTargetVertex e))
            (controlDisks.vertexRadius (edgeTargetVertex e)) ∧
        targetBoundaryPoint e ∈ D.edgeCarrier e
  sourceBoundary_unique :
    ∀ e p,
      p ∈ Metric.sphere (D.vertexPlacement (edgeSourceVertex e))
          (controlDisks.vertexRadius (edgeSourceVertex e)) →
        p ∈ D.edgeCarrier e → p = sourceBoundaryPoint e
  targetBoundary_unique :
    ∀ e p,
      p ∈ Metric.sphere (D.vertexPlacement (edgeTargetVertex e))
          (controlDisks.vertexRadius (edgeTargetVertex e)) →
        p ∈ D.edgeCarrier e → p = targetBoundaryPoint e
