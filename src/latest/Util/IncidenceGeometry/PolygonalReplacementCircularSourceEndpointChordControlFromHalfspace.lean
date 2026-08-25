import Util.IncidenceGeometry.PolygonalReplacementSourceEndpointControlDiskNeighborhood
import Util.IncidenceGeometry.PolygonalReplacementCircularEndpointSupportingHalfspace
import Mathlib.Analysis.InnerProductSpace.Convex

open Classical
noncomputable section

universe u

lemma PolygonalReplacementCircularSourceEndpointChordControlFromHalfspace {V : Type u}
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
    (tube_open : ∀ i, IsOpen (tube i))
    (originalPiece_subset_tube :
      ∀ i, residualPieceData.originalPiece i ⊆ tube i)
    (i : residualPieceData.pieceIndex)
    (vertex_halfspace_point :
      ∀ (v : V) (ε : ℝ),
        v ∈ (residualPieceData.owner i).1 →
          residualPieceData.source i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
          residualPieceData.source i ∈ D.edgeCarrier (residualPieceData.owner i) →
          0 < ε →
            ∃ u : Set.Icc (0 : ℝ) 1,
              residualPieceData.sourceParam i < u ∧
                u ≤ residualPieceData.targetParam i ∧
                  residualPieceData.edgeParam (residualPieceData.owner i) u ∈
                    Metric.ball (residualPieceData.source i) ε ∧
                  (controlDisks.vertexRadius v) ^ 2 ≤
                    inner ℝ
                      (residualPieceData.edgeParam (residualPieceData.owner i) u -
                        D.vertexPlacement v)
                      (residualPieceData.source i - D.vertexPlacement v))
    (intersection_halfspace_point :
      ∀ (x : {p // p ∈ D.intersectionPoints}) (ε : ℝ),
        x.1 ∈ D.edgeRelativeInterior (residualPieceData.owner i) →
          residualPieceData.source i ∈
            Metric.sphere x.1 (controlDisks.intersectionRadius x) →
          residualPieceData.source i ∈ D.edgeCarrier (residualPieceData.owner i) →
          0 < ε →
            ∃ u : Set.Icc (0 : ℝ) 1,
              residualPieceData.sourceParam i < u ∧
                u ≤ residualPieceData.targetParam i ∧
                  residualPieceData.edgeParam (residualPieceData.owner i) u ∈
                    Metric.ball (residualPieceData.source i) ε ∧
                  (controlDisks.intersectionRadius x) ^ 2 ≤
                    inner ℝ
                      (residualPieceData.edgeParam (residualPieceData.owner i) u -
                        x.1)
                      (residualPieceData.source i - x.1)) :
    (∃ v : V,
        v ∈ (residualPieceData.owner i).1 ∧
          residualPieceData.source i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
          residualPieceData.source i ∈
            D.edgeCarrier (residualPieceData.owner i) ∧
          ∃ u : Set.Icc (0 : ℝ) 1,
            residualPieceData.sourceParam i < u ∧
              u ≤ residualPieceData.targetParam i ∧
              let b :=
                residualPieceData.edgeParam (residualPieceData.owner i) u
              b ∈ tube i ∧
                segment ℝ (residualPieceData.source i) b ⊆ tube i ∧
                (∀ p : EuclideanSpace ℝ (Fin 2),
                  p ∈ segment ℝ (residualPieceData.source i) b →
                    p ∈ Metric.closedBall (D.vertexPlacement v)
                        (controlDisks.vertexRadius v) →
                      p = residualPieceData.source i) ∧
                Disjoint (openSegment ℝ (residualPieceData.source i) b)
                  (Metric.ball (D.vertexPlacement v)
                    (controlDisks.vertexRadius v)) ∧
                (∀ w : V, w ≠ v →
                  Disjoint (segment ℝ (residualPieceData.source i) b)
                    (Metric.closedBall (D.vertexPlacement w)
                      (controlDisks.vertexRadius w))) ∧
                (∀ x : {p // p ∈ D.intersectionPoints},
                  Disjoint (segment ℝ (residualPieceData.source i) b)
                    (Metric.closedBall x.1
                      (controlDisks.intersectionRadius x)))) ∨
      (∃ x : {p // p ∈ D.intersectionPoints},
        x.1 ∈ D.edgeRelativeInterior (residualPieceData.owner i) ∧
          residualPieceData.source i ∈
            Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
          residualPieceData.source i ∈
            D.edgeCarrier (residualPieceData.owner i) ∧
          ∃ u : Set.Icc (0 : ℝ) 1,
            residualPieceData.sourceParam i < u ∧
              u ≤ residualPieceData.targetParam i ∧
              let b :=
                residualPieceData.edgeParam (residualPieceData.owner i) u
              b ∈ tube i ∧
                segment ℝ (residualPieceData.source i) b ⊆ tube i ∧
                (∀ p : EuclideanSpace ℝ (Fin 2),
                  p ∈ segment ℝ (residualPieceData.source i) b →
                    p ∈ Metric.closedBall x.1
                        (controlDisks.intersectionRadius x) →
                      p = residualPieceData.source i) ∧
                Disjoint (openSegment ℝ (residualPieceData.source i) b)
                  (Metric.ball x.1 (controlDisks.intersectionRadius x)) ∧
                (∀ v : V,
                  Disjoint (segment ℝ (residualPieceData.source i) b)
                    (Metric.closedBall (D.vertexPlacement v)
                      (controlDisks.vertexRadius v))) ∧
                (∀ y : {p // p ∈ D.intersectionPoints}, y ≠ x →
                  Disjoint (segment ℝ (residualPieceData.source i) b)
                    (Metric.closedBall y.1
                      (controlDisks.intersectionRadius y)))) := by
  classical
  have source_control :=
    PolygonalReplacementSourceEndpointControlDiskNeighborhood G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData tube tube_open
      originalPiece_subset_tube i
  rcases source_control with
    ⟨v, hv_owner, hv_sphere, hv_carrier, ε, hε_pos, hε_tube,
      hε_vertex_disjoint, hε_intersection_disjoint⟩ |
    ⟨x, hx_rel, hx_sphere, hx_carrier, ε, hε_pos, hε_tube,
      hε_vertex_disjoint, hε_intersection_disjoint⟩
  · rcases vertex_halfspace_point v ε hv_owner hv_sphere hv_carrier hε_pos with
      ⟨u, hu_source, hu_target, hb_ball, hhalfspace⟩
    let b : EuclideanSpace ℝ (Fin 2) :=
      residualPieceData.edgeParam (residualPieceData.owner i) u
    have hsource_ball :
        residualPieceData.source i ∈
          Metric.ball (residualPieceData.source i) ε := by
      rw [Metric.mem_ball, dist_self]
      exact hε_pos
    have hb_ball' : b ∈ Metric.ball (residualPieceData.source i) ε := by
      simpa [b] using hb_ball
    have hseg_ball :
        segment ℝ (residualPieceData.source i) b ⊆
          Metric.ball (residualPieceData.source i) ε :=
      (convex_ball (residualPieceData.source i) ε).segment_subset
        hsource_ball hb_ball'
    have hb_tube : b ∈ tube i := hε_tube hb_ball'
    have hseg_tube :
        segment ℝ (residualPieceData.source i) b ⊆ tube i := by
      intro p hp
      exact hε_tube (hseg_ball hp)
    have hsupp :=
      PolygonalReplacementCircularEndpointSupportingHalfspace
        (le_of_lt (controlDisks.vertexRadius_pos v)) hv_sphere
        (by simpa [b] using hhalfspace)
    left
    refine ⟨v, hv_owner, hv_sphere, hv_carrier, u, hu_source, hu_target, ?_⟩
    dsimp only
    refine ⟨by simpa [b] using hb_tube, by simpa [b] using hseg_tube,
      ?_, by simpa [b] using hsupp.2, ?_, ?_⟩
    · intro p hpseg hpclosed
      exact hsupp.1 p (by simpa [b] using hpseg) hpclosed
    · intro w hw
      rw [Set.disjoint_left]
      intro p hpseg hpclosed
      exact (Set.disjoint_left.mp (hε_vertex_disjoint w hw))
        (hseg_ball (by simpa [b] using hpseg)) hpclosed
    · intro x
      rw [Set.disjoint_left]
      intro p hpseg hpclosed
      exact (Set.disjoint_left.mp (hε_intersection_disjoint x))
        (hseg_ball (by simpa [b] using hpseg)) hpclosed
  · rcases intersection_halfspace_point x ε hx_rel hx_sphere hx_carrier hε_pos with
      ⟨u, hu_source, hu_target, hb_ball, hhalfspace⟩
    let b : EuclideanSpace ℝ (Fin 2) :=
      residualPieceData.edgeParam (residualPieceData.owner i) u
    have hsource_ball :
        residualPieceData.source i ∈
          Metric.ball (residualPieceData.source i) ε := by
      rw [Metric.mem_ball, dist_self]
      exact hε_pos
    have hb_ball' : b ∈ Metric.ball (residualPieceData.source i) ε := by
      simpa [b] using hb_ball
    have hseg_ball :
        segment ℝ (residualPieceData.source i) b ⊆
          Metric.ball (residualPieceData.source i) ε :=
      (convex_ball (residualPieceData.source i) ε).segment_subset
        hsource_ball hb_ball'
    have hb_tube : b ∈ tube i := hε_tube hb_ball'
    have hseg_tube :
        segment ℝ (residualPieceData.source i) b ⊆ tube i := by
      intro p hp
      exact hε_tube (hseg_ball hp)
    have hsupp :=
      PolygonalReplacementCircularEndpointSupportingHalfspace
        (le_of_lt (controlDisks.intersectionRadius_pos x)) hx_sphere
        (by simpa [b] using hhalfspace)
    right
    refine ⟨x, hx_rel, hx_sphere, hx_carrier, u, hu_source, hu_target, ?_⟩
    dsimp only
    refine ⟨by simpa [b] using hb_tube, by simpa [b] using hseg_tube,
      ?_, by simpa [b] using hsupp.2, ?_, ?_⟩
    · intro p hpseg hpclosed
      exact hsupp.1 p (by simpa [b] using hpseg) hpclosed
    · intro v
      rw [Set.disjoint_left]
      intro p hpseg hpclosed
      exact (Set.disjoint_left.mp (hε_vertex_disjoint v))
        (hseg_ball (by simpa [b] using hpseg)) hpclosed
    · intro y hy
      rw [Set.disjoint_left]
      intro p hpseg hpclosed
      exact (Set.disjoint_left.mp (hε_intersection_disjoint y hy))
        (hseg_ball (by simpa [b] using hpseg)) hpclosed
