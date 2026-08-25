import Util.IncidenceGeometry.PolygonalReplacementResidualPieceData

open Classical
noncomputable section

universe u

lemma PolygonalReplacementResidualOriginalPieceClosedBallContactOnlyEndpoint
    {V : Type u} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (residualPieceData :
      PolygonalReplacementResidualPieceData G D controlDisks boundaryPoints
        edgeEndpoints) :
    (∀ (i : residualPieceData.pieceIndex) (v : V)
        (p : EuclideanSpace ℝ (Fin 2)),
      p ∈ residualPieceData.originalPiece i →
        p ∈ Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v) →
          (p = residualPieceData.source i ∧
              residualPieceData.source i ∈
                Metric.sphere (D.vertexPlacement v)
                  (controlDisks.vertexRadius v)) ∨
            (p = residualPieceData.target i ∧
              residualPieceData.target i ∈
                Metric.sphere (D.vertexPlacement v)
                  (controlDisks.vertexRadius v))) ∧
      (∀ (i : residualPieceData.pieceIndex)
        (x : {p // p ∈ D.intersectionPoints})
        (p : EuclideanSpace ℝ (Fin 2)),
      p ∈ residualPieceData.originalPiece i →
        p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) →
          (p = residualPieceData.source i ∧
              residualPieceData.source i ∈
                Metric.sphere x.1 (controlDisks.intersectionRadius x)) ∨
            (p = residualPieceData.target i ∧
              residualPieceData.target i ∈
                Metric.sphere x.1 (controlDisks.intersectionRadius x))) := by
  classical
  constructor
  · intro i v p hpOriginal hpClosed
    have hpNotBall :
        p ∉ Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v) := by
      intro hpBall
      exact
        (Set.disjoint_left.mp
          (residualPieceData.originalPiece_avoids_vertex_disk_interiors i v))
          hpOriginal hpBall
    have hpSphere :
        p ∈ Metric.sphere (D.vertexPlacement v)
          (controlDisks.vertexRadius v) := by
      rw [Metric.mem_sphere]
      have hle :
          dist p (D.vertexPlacement v) ≤ controlDisks.vertexRadius v := by
        simpa [Metric.mem_closedBall] using hpClosed
      have hnlt :
          ¬ dist p (D.vertexPlacement v) < controlDisks.vertexRadius v := by
        simpa [Metric.mem_ball] using hpNotBall
      exact le_antisymm hle (le_of_not_gt hnlt)
    have hpCarrierOwner : p ∈ D.edgeCarrier (residualPieceData.owner i) :=
      residualPieceData.originalPiece_subset_owner i hpOriginal
    have hv_mem : v ∈ (residualPieceData.owner i).1 :=
      controlDisks.vertex_disk_meets_only_incident_edges hpClosed hpCarrierOwner
    rcases residualPieceData.vertex_boundary_attached hv_mem hpSphere
        hpCarrierOwner with
      ⟨j, hj, _huniq⟩
    have hpOriginal_j : p ∈ residualPieceData.originalPiece j := by
      rcases hj.2 with hsrc | htgt
      · simpa [hsrc] using residualPieceData.source_mem_originalPiece j
      · simpa [htgt] using residualPieceData.target_mem_originalPiece j
    have hji : j = i := by
      by_contra hne
      exact
        (Set.disjoint_left.mp
          (residualPieceData.originalPieces_pairwise_disjoint hne))
          hpOriginal_j hpOriginal
    subst j
    rcases hj.2 with hsrc | htgt
    · left
      exact ⟨hsrc.symm, by simpa [hsrc] using hpSphere⟩
    · right
      exact ⟨htgt.symm, by simpa [htgt] using hpSphere⟩
  · intro i x p hpOriginal hpClosed
    have hpNotBall :
        p ∉ Metric.ball x.1 (controlDisks.intersectionRadius x) := by
      intro hpBall
      exact
        (Set.disjoint_left.mp
          (residualPieceData.originalPiece_avoids_intersection_disk_interiors i x))
          hpOriginal hpBall
    have hpSphere :
        p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
      rw [Metric.mem_sphere]
      have hle :
          dist p x.1 ≤ controlDisks.intersectionRadius x := by
        simpa [Metric.mem_closedBall] using hpClosed
      have hnlt :
          ¬ dist p x.1 < controlDisks.intersectionRadius x := by
        simpa [Metric.mem_ball] using hpNotBall
      exact le_antisymm hle (le_of_not_gt hnlt)
    have hpCarrierOwner : p ∈ D.edgeCarrier (residualPieceData.owner i) :=
      residualPieceData.originalPiece_subset_owner i hpOriginal
    have hx_mem : x.1 ∈ D.edgeRelativeInterior (residualPieceData.owner i) :=
      controlDisks.intersection_disk_meets_only_passing_edges hpClosed
        hpCarrierOwner
    rcases residualPieceData.intersection_boundary_attached hx_mem hpSphere
        hpCarrierOwner with
      ⟨j, hj, _huniq⟩
    have hpOriginal_j : p ∈ residualPieceData.originalPiece j := by
      rcases hj.2 with hsrc | htgt
      · simpa [hsrc] using residualPieceData.source_mem_originalPiece j
      · simpa [htgt] using residualPieceData.target_mem_originalPiece j
    have hji : j = i := by
      by_contra hne
      exact
        (Set.disjoint_left.mp
          (residualPieceData.originalPieces_pairwise_disjoint hne))
          hpOriginal_j hpOriginal
    subst j
    rcases hj.2 with hsrc | htgt
    · left
      exact ⟨hsrc.symm, by simpa [hsrc] using hpSphere⟩
    · right
      exact ⟨htgt.symm, by simpa [htgt] using hpSphere⟩
