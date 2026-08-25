import Util.IncidenceGeometry.PolygonalReplacementStraightResidualPieceSegment
import Util.IncidenceGeometry.StraightSegmentPolygonalArc

open Classical
noncomputable section

universe u

lemma PolygonalReplacementStraightResidualPieceChainInTube {V : Type u}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (residualPieceData :
      PolygonalReplacementResidualPieceData G D controlDisks boundaryPoints
        edgeEndpoints)
    (tube : residualPieceData.pieceIndex → Set (EuclideanSpace ℝ (Fin 2)))
    (_tube_open : ∀ i, IsOpen (tube i))
    (originalPiece_subset_tube :
      ∀ i, residualPieceData.originalPiece i ⊆ tube i)
    (i : residualPieceData.pieceIndex)
    (hstraight :
      (D.edgeSource (residualPieceData.owner i) ≠
          D.edgeTarget (residualPieceData.owner i)) ∧
        D.edgeCarrier (residualPieceData.owner i) =
          segment ℝ (D.edgeSource (residualPieceData.owner i))
            (D.edgeTarget (residualPieceData.owner i)) ∧
        D.edgeRelativeInterior (residualPieceData.owner i) =
          openSegment ℝ (D.edgeSource (residualPieceData.owner i))
            (D.edgeTarget (residualPieceData.owner i))) :
    ∃ Γ : PolygonalArc,
      Γ.source = residualPieceData.source i ∧
        Γ.target = residualPieceData.target i ∧
          Γ.carrier ⊆ tube i ∧
            (∀ v : V,
              Disjoint Γ.relativeInterior
                (Metric.ball (D.vertexPlacement v)
                  (controlDisks.vertexRadius v))) ∧
            (∀ x : {p // p ∈ D.intersectionPoints},
              Disjoint Γ.relativeInterior
                (Metric.ball x.1 (controlDisks.intersectionRadius x))) ∧
            (∀ v p,
              p ∈ Γ.carrier →
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
            (∀ x : {p // p ∈ D.intersectionPoints}, ∀ p,
              p ∈ Γ.carrier →
                p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) →
                  (p = residualPieceData.source i ∧
                      residualPieceData.source i ∈
                        Metric.sphere x.1
                          (controlDisks.intersectionRadius x)) ∨
                    (p = residualPieceData.target i ∧
                      residualPieceData.target i ∈
                        Metric.sphere x.1
                          (controlDisks.intersectionRadius x))) := by
  classical
  have originalPiece_eq_segment :
      residualPieceData.originalPiece i =
        segment ℝ (residualPieceData.source i) (residualPieceData.target i) :=
    PolygonalReplacementStraightResidualPieceSegment G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData i hstraight
  obtain ⟨Γ, hΓ_source, hΓ_target, hΓ_carrier, hΓ_rel⟩ :=
    StraightSegmentPolygonalArc (residualPieceData.source i)
      (residualPieceData.target i) (residualPieceData.source_ne_target i)
  have carrier_subset_original :
      Γ.carrier ⊆ residualPieceData.originalPiece i := by
    intro p hp
    rw [hΓ_carrier] at hp
    simpa [originalPiece_eq_segment] using hp
  have rel_subset_original :
      Γ.relativeInterior ⊆ residualPieceData.originalPiece i := by
    intro p hp
    have hpCarrier : p ∈ Γ.carrier := by
      rw [hΓ_rel] at hp
      have hpSegment :
          p ∈ segment ℝ (residualPieceData.source i)
            (residualPieceData.target i) :=
        openSegment_subset_segment ℝ (residualPieceData.source i)
          (residualPieceData.target i) hp
      simpa [hΓ_carrier] using hpSegment
    exact carrier_subset_original hpCarrier
  refine ⟨Γ, hΓ_source, hΓ_target, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact originalPiece_subset_tube i (carrier_subset_original hp)
  · intro v
    rw [Set.disjoint_left]
    intro p hpRel hpBall
    exact
      (Set.disjoint_left.mp
        (residualPieceData.originalPiece_avoids_vertex_disk_interiors i v))
        (rel_subset_original hpRel) hpBall
  · intro x
    rw [Set.disjoint_left]
    intro p hpRel hpBall
    exact
      (Set.disjoint_left.mp
        (residualPieceData.originalPiece_avoids_intersection_disk_interiors i x))
        (rel_subset_original hpRel) hpBall
  · intro v p hpCarrier hpClosed
    have hpOriginal : p ∈ residualPieceData.originalPiece i :=
      carrier_subset_original hpCarrier
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
  · intro x p hpCarrier hpClosed
    have hpOriginal : p ∈ residualPieceData.originalPiece i :=
      carrier_subset_original hpCarrier
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
