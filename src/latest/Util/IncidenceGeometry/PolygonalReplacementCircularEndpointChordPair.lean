import Util.IncidenceGeometry.PolygonalReplacementResidualPieceEndpointParameterSeparation
import Util.IncidenceGeometry.PolygonalReplacementSourceEndpointControlDiskNeighborhood
import Util.IncidenceGeometry.PolygonalReplacementTargetEndpointControlDiskNeighborhood
import Util.IncidenceGeometry.PolygonalReplacementCircularSourceRetainedHalfspacePoint
import Util.IncidenceGeometry.PolygonalReplacementCircularTargetRetainedHalfspacePoint
import Util.IncidenceGeometry.PolygonalReplacementCircularEndpointSupportingHalfspace
import Mathlib.Analysis.InnerProductSpace.Convex

open Classical
noncomputable section

universe u


lemma PolygonalReplacementCircularEndpointChordPair {V : Type u}
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
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)}
    (hcircular :
      0 < r ∧
        Continuous γ ∧ Function.Injective γ ∧
        (∀ t, dist (γ t) c = r) ∧
        γ ⟨0, by simp⟩ = D.edgeSource (residualPieceData.owner i) ∧
        γ ⟨1, by simp⟩ = D.edgeTarget (residualPieceData.owner i) ∧
        D.edgeCarrier (residualPieceData.owner i) = Set.range γ ∧
        D.edgeRelativeInterior (residualPieceData.owner i) =
          Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
            γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)) :
    ∃ us ut : Set.Icc (0 : ℝ) 1,
      residualPieceData.sourceParam i < us ∧
        us < ut ∧
          ut < residualPieceData.targetParam i ∧
          (((∃ v : V,
              v ∈ (residualPieceData.owner i).1 ∧
                residualPieceData.source i ∈
                  Metric.sphere (D.vertexPlacement v)
                    (controlDisks.vertexRadius v) ∧
                residualPieceData.source i ∈
                  D.edgeCarrier (residualPieceData.owner i) ∧
                let b :=
                  residualPieceData.edgeParam (residualPieceData.owner i) us
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
                let b :=
                  residualPieceData.edgeParam (residualPieceData.owner i) us
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
                        (controlDisks.intersectionRadius y))))) ∧
            ((∃ v : V,
              v ∈ (residualPieceData.owner i).1 ∧
                residualPieceData.target i ∈
                  Metric.sphere (D.vertexPlacement v)
                    (controlDisks.vertexRadius v) ∧
                residualPieceData.target i ∈
                  D.edgeCarrier (residualPieceData.owner i) ∧
                let b :=
                  residualPieceData.edgeParam (residualPieceData.owner i) ut
                b ∈ tube i ∧
                  segment ℝ (residualPieceData.target i) b ⊆ tube i ∧
                  (∀ p : EuclideanSpace ℝ (Fin 2),
                    p ∈ segment ℝ (residualPieceData.target i) b →
                      p ∈ Metric.closedBall (D.vertexPlacement v)
                          (controlDisks.vertexRadius v) →
                        p = residualPieceData.target i) ∧
                  Disjoint (openSegment ℝ (residualPieceData.target i) b)
                    (Metric.ball (D.vertexPlacement v)
                      (controlDisks.vertexRadius v)) ∧
                  (∀ w : V, w ≠ v →
                    Disjoint (segment ℝ (residualPieceData.target i) b)
                      (Metric.closedBall (D.vertexPlacement w)
                        (controlDisks.vertexRadius w))) ∧
                  (∀ x : {p // p ∈ D.intersectionPoints},
                    Disjoint (segment ℝ (residualPieceData.target i) b)
                      (Metric.closedBall x.1
                        (controlDisks.intersectionRadius x)))) ∨
            (∃ x : {p // p ∈ D.intersectionPoints},
              x.1 ∈ D.edgeRelativeInterior (residualPieceData.owner i) ∧
                residualPieceData.target i ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                residualPieceData.target i ∈
                  D.edgeCarrier (residualPieceData.owner i) ∧
                let b :=
                  residualPieceData.edgeParam (residualPieceData.owner i) ut
                b ∈ tube i ∧
                  segment ℝ (residualPieceData.target i) b ⊆ tube i ∧
                  (∀ p : EuclideanSpace ℝ (Fin 2),
                    p ∈ segment ℝ (residualPieceData.target i) b →
                      p ∈ Metric.closedBall x.1
                          (controlDisks.intersectionRadius x) →
                        p = residualPieceData.target i) ∧
                  Disjoint (openSegment ℝ (residualPieceData.target i) b)
                    (Metric.ball x.1 (controlDisks.intersectionRadius x)) ∧
                  (∀ v : V,
                    Disjoint (segment ℝ (residualPieceData.target i) b)
                      (Metric.closedBall (D.vertexPlacement v)
                        (controlDisks.vertexRadius v))) ∧
                  (∀ y : {p // p ∈ D.intersectionPoints}, y ≠ x →
                    Disjoint (segment ℝ (residualPieceData.target i) b)
                      (Metric.closedBall y.1
                        (controlDisks.intersectionRadius y)))))) := by
  classical
  obtain ⟨m, hsource_m, hm_target, εs, hεs_pos, hsource_ball_left,
      εt, hεt_pos, htarget_ball_right⟩ :=
    PolygonalReplacementResidualPieceEndpointParameterSeparation G D
      controlDisks boundaryPoints edgeEndpoints residualPieceData i
  have source_halfspace :=
    PolygonalReplacementCircularSourceRetainedHalfspacePoint G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData i hcircular
  have target_halfspace :=
    PolygonalReplacementCircularTargetRetainedHalfspacePoint G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData i hcircular
  have source_control :=
    PolygonalReplacementSourceEndpointControlDiskNeighborhood G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData tube tube_open
      originalPiece_subset_tube i
  have target_control :=
    PolygonalReplacementTargetEndpointControlDiskNeighborhood G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData tube tube_open
      originalPiece_subset_tube i
  have source_pack :
      ∃ us : Set.Icc (0 : ℝ) 1,
        residualPieceData.sourceParam i < us ∧
          us < m ∧
          ((∃ v : V,
              v ∈ (residualPieceData.owner i).1 ∧
                residualPieceData.source i ∈
                  Metric.sphere (D.vertexPlacement v)
                    (controlDisks.vertexRadius v) ∧
                residualPieceData.source i ∈
                  D.edgeCarrier (residualPieceData.owner i) ∧
                let b :=
                  residualPieceData.edgeParam (residualPieceData.owner i) us
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
                let b :=
                  residualPieceData.edgeParam (residualPieceData.owner i) us
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
                        (controlDisks.intersectionRadius y))))) := by
    rcases source_control with
      ⟨v, hv_owner, hv_sphere, hv_carrier, ρ, hρ_pos, hρ_tube,
        hρ_vertex_disjoint, hρ_intersection_disjoint⟩ |
      ⟨x, hx_rel, hx_sphere, hx_carrier, ρ, hρ_pos, hρ_tube,
        hρ_vertex_disjoint, hρ_intersection_disjoint⟩
    · let η : ℝ := min ρ εs
      have hη_pos : 0 < η := lt_min hρ_pos hεs_pos
      have hη_le_ρ : η ≤ ρ := min_le_left _ _
      have hη_le_εs : η ≤ εs := min_le_right _ _
      rcases source_halfspace.1 v η hv_owner hv_sphere hv_carrier hη_pos with
        ⟨u, hu_source, hu_target, hb_ballη, hhalfspace⟩
      let b : EuclideanSpace ℝ (Fin 2) :=
        residualPieceData.edgeParam (residualPieceData.owner i) u
      have hb_ballρ : b ∈ Metric.ball (residualPieceData.source i) ρ := by
        rw [Metric.mem_ball] at hb_ballη ⊢
        exact lt_of_lt_of_le (by simpa [b] using hb_ballη) hη_le_ρ
      have hb_ballεs :
          b ∈ Metric.ball (residualPieceData.source i) εs := by
        rw [Metric.mem_ball] at hb_ballη ⊢
        exact lt_of_lt_of_le (by simpa [b] using hb_ballη) hη_le_εs
      have hu_lt_m : u < m := hsource_ball_left u hu_target
        (by simpa [b] using hb_ballεs)
      have hsource_ball :
          residualPieceData.source i ∈
            Metric.ball (residualPieceData.source i) ρ := by
        rw [Metric.mem_ball, dist_self]
        exact hρ_pos
      have hseg_ball :
          segment ℝ (residualPieceData.source i) b ⊆
            Metric.ball (residualPieceData.source i) ρ :=
        (convex_ball (residualPieceData.source i) ρ).segment_subset
          hsource_ball hb_ballρ
      have hb_tube : b ∈ tube i := hρ_tube hb_ballρ
      have hseg_tube :
          segment ℝ (residualPieceData.source i) b ⊆ tube i := by
        intro p hp
        exact hρ_tube (hseg_ball hp)
      have hsupp :=
        PolygonalReplacementCircularEndpointSupportingHalfspace
          (le_of_lt (controlDisks.vertexRadius_pos v)) hv_sphere
          (by simpa [b] using hhalfspace)
      refine ⟨u, hu_source, hu_lt_m, Or.inl ?_⟩
      refine ⟨v, hv_owner, hv_sphere, hv_carrier, ?_⟩
      dsimp only
      refine ⟨by simpa [b] using hb_tube, by simpa [b] using hseg_tube,
        ?_, by simpa [b] using hsupp.2, ?_, ?_⟩
      · intro p hpseg hpclosed
        exact hsupp.1 p (by simpa [b] using hpseg) hpclosed
      · intro w hw
        rw [Set.disjoint_left]
        intro p hpseg hpclosed
        exact (Set.disjoint_left.mp (hρ_vertex_disjoint w hw))
          (hseg_ball (by simpa [b] using hpseg)) hpclosed
      · intro x
        rw [Set.disjoint_left]
        intro p hpseg hpclosed
        exact (Set.disjoint_left.mp (hρ_intersection_disjoint x))
          (hseg_ball (by simpa [b] using hpseg)) hpclosed
    · let η : ℝ := min ρ εs
      have hη_pos : 0 < η := lt_min hρ_pos hεs_pos
      have hη_le_ρ : η ≤ ρ := min_le_left _ _
      have hη_le_εs : η ≤ εs := min_le_right _ _
      rcases source_halfspace.2 x η hx_rel hx_sphere hx_carrier hη_pos with
        ⟨u, hu_source, hu_target, hb_ballη, hhalfspace⟩
      let b : EuclideanSpace ℝ (Fin 2) :=
        residualPieceData.edgeParam (residualPieceData.owner i) u
      have hb_ballρ : b ∈ Metric.ball (residualPieceData.source i) ρ := by
        rw [Metric.mem_ball] at hb_ballη ⊢
        exact lt_of_lt_of_le (by simpa [b] using hb_ballη) hη_le_ρ
      have hb_ballεs :
          b ∈ Metric.ball (residualPieceData.source i) εs := by
        rw [Metric.mem_ball] at hb_ballη ⊢
        exact lt_of_lt_of_le (by simpa [b] using hb_ballη) hη_le_εs
      have hu_lt_m : u < m := hsource_ball_left u hu_target
        (by simpa [b] using hb_ballεs)
      have hsource_ball :
          residualPieceData.source i ∈
            Metric.ball (residualPieceData.source i) ρ := by
        rw [Metric.mem_ball, dist_self]
        exact hρ_pos
      have hseg_ball :
          segment ℝ (residualPieceData.source i) b ⊆
            Metric.ball (residualPieceData.source i) ρ :=
        (convex_ball (residualPieceData.source i) ρ).segment_subset
          hsource_ball hb_ballρ
      have hb_tube : b ∈ tube i := hρ_tube hb_ballρ
      have hseg_tube :
          segment ℝ (residualPieceData.source i) b ⊆ tube i := by
        intro p hp
        exact hρ_tube (hseg_ball hp)
      have hsupp :=
        PolygonalReplacementCircularEndpointSupportingHalfspace
          (le_of_lt (controlDisks.intersectionRadius_pos x)) hx_sphere
          (by simpa [b] using hhalfspace)
      refine ⟨u, hu_source, hu_lt_m, Or.inr ?_⟩
      refine ⟨x, hx_rel, hx_sphere, hx_carrier, ?_⟩
      dsimp only
      refine ⟨by simpa [b] using hb_tube, by simpa [b] using hseg_tube,
        ?_, by simpa [b] using hsupp.2, ?_, ?_⟩
      · intro p hpseg hpclosed
        exact hsupp.1 p (by simpa [b] using hpseg) hpclosed
      · intro v
        rw [Set.disjoint_left]
        intro p hpseg hpclosed
        exact (Set.disjoint_left.mp (hρ_vertex_disjoint v))
          (hseg_ball (by simpa [b] using hpseg)) hpclosed
      · intro y hy
        rw [Set.disjoint_left]
        intro p hpseg hpclosed
        exact (Set.disjoint_left.mp (hρ_intersection_disjoint y hy))
          (hseg_ball (by simpa [b] using hpseg)) hpclosed
  have target_pack :
      ∃ ut : Set.Icc (0 : ℝ) 1,
        m < ut ∧
          ut < residualPieceData.targetParam i ∧
          ((∃ v : V,
              v ∈ (residualPieceData.owner i).1 ∧
                residualPieceData.target i ∈
                  Metric.sphere (D.vertexPlacement v)
                    (controlDisks.vertexRadius v) ∧
                residualPieceData.target i ∈
                  D.edgeCarrier (residualPieceData.owner i) ∧
                let b :=
                  residualPieceData.edgeParam (residualPieceData.owner i) ut
                b ∈ tube i ∧
                  segment ℝ (residualPieceData.target i) b ⊆ tube i ∧
                  (∀ p : EuclideanSpace ℝ (Fin 2),
                    p ∈ segment ℝ (residualPieceData.target i) b →
                      p ∈ Metric.closedBall (D.vertexPlacement v)
                          (controlDisks.vertexRadius v) →
                        p = residualPieceData.target i) ∧
                  Disjoint (openSegment ℝ (residualPieceData.target i) b)
                    (Metric.ball (D.vertexPlacement v)
                      (controlDisks.vertexRadius v)) ∧
                  (∀ w : V, w ≠ v →
                    Disjoint (segment ℝ (residualPieceData.target i) b)
                      (Metric.closedBall (D.vertexPlacement w)
                        (controlDisks.vertexRadius w))) ∧
                  (∀ x : {p // p ∈ D.intersectionPoints},
                    Disjoint (segment ℝ (residualPieceData.target i) b)
                      (Metric.closedBall x.1
                        (controlDisks.intersectionRadius x)))) ∨
            (∃ x : {p // p ∈ D.intersectionPoints},
              x.1 ∈ D.edgeRelativeInterior (residualPieceData.owner i) ∧
                residualPieceData.target i ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                residualPieceData.target i ∈
                  D.edgeCarrier (residualPieceData.owner i) ∧
                let b :=
                  residualPieceData.edgeParam (residualPieceData.owner i) ut
                b ∈ tube i ∧
                  segment ℝ (residualPieceData.target i) b ⊆ tube i ∧
                  (∀ p : EuclideanSpace ℝ (Fin 2),
                    p ∈ segment ℝ (residualPieceData.target i) b →
                      p ∈ Metric.closedBall x.1
                          (controlDisks.intersectionRadius x) →
                        p = residualPieceData.target i) ∧
                  Disjoint (openSegment ℝ (residualPieceData.target i) b)
                    (Metric.ball x.1 (controlDisks.intersectionRadius x)) ∧
                  (∀ v : V,
                    Disjoint (segment ℝ (residualPieceData.target i) b)
                      (Metric.closedBall (D.vertexPlacement v)
                        (controlDisks.vertexRadius v))) ∧
                  (∀ y : {p // p ∈ D.intersectionPoints}, y ≠ x →
                    Disjoint (segment ℝ (residualPieceData.target i) b)
                      (Metric.closedBall y.1
                        (controlDisks.intersectionRadius y))))) := by
    rcases target_control with
      ⟨v, hv_owner, hv_sphere, hv_carrier, ρ, hρ_pos, hρ_tube,
        hρ_vertex_disjoint, hρ_intersection_disjoint⟩ |
      ⟨x, hx_rel, hx_sphere, hx_carrier, ρ, hρ_pos, hρ_tube,
        hρ_vertex_disjoint, hρ_intersection_disjoint⟩
    · let η : ℝ := min ρ εt
      have hη_pos : 0 < η := lt_min hρ_pos hεt_pos
      have hη_le_ρ : η ≤ ρ := min_le_left _ _
      have hη_le_εt : η ≤ εt := min_le_right _ _
      rcases target_halfspace.1 v η hv_owner hv_sphere hv_carrier hη_pos with
        ⟨u, hu_source, hu_target, hb_ballη, hhalfspace⟩
      let b : EuclideanSpace ℝ (Fin 2) :=
        residualPieceData.edgeParam (residualPieceData.owner i) u
      have hb_ballρ : b ∈ Metric.ball (residualPieceData.target i) ρ := by
        rw [Metric.mem_ball] at hb_ballη ⊢
        exact lt_of_lt_of_le (by simpa [b] using hb_ballη) hη_le_ρ
      have hb_ballεt :
          b ∈ Metric.ball (residualPieceData.target i) εt := by
        rw [Metric.mem_ball] at hb_ballη ⊢
        exact lt_of_lt_of_le (by simpa [b] using hb_ballη) hη_le_εt
      have hm_lt_u : m < u := htarget_ball_right u hu_source
        (by simpa [b] using hb_ballεt)
      have htarget_ball :
          residualPieceData.target i ∈
            Metric.ball (residualPieceData.target i) ρ := by
        rw [Metric.mem_ball, dist_self]
        exact hρ_pos
      have hseg_ball :
          segment ℝ (residualPieceData.target i) b ⊆
            Metric.ball (residualPieceData.target i) ρ :=
        (convex_ball (residualPieceData.target i) ρ).segment_subset
          htarget_ball hb_ballρ
      have hb_tube : b ∈ tube i := hρ_tube hb_ballρ
      have hseg_tube :
          segment ℝ (residualPieceData.target i) b ⊆ tube i := by
        intro p hp
        exact hρ_tube (hseg_ball hp)
      have hsupp :=
        PolygonalReplacementCircularEndpointSupportingHalfspace
          (le_of_lt (controlDisks.vertexRadius_pos v)) hv_sphere
          (by simpa [b] using hhalfspace)
      refine ⟨u, hm_lt_u, hu_target, Or.inl ?_⟩
      refine ⟨v, hv_owner, hv_sphere, hv_carrier, ?_⟩
      dsimp only
      refine ⟨by simpa [b] using hb_tube, by simpa [b] using hseg_tube,
        ?_, by simpa [b] using hsupp.2, ?_, ?_⟩
      · intro p hpseg hpclosed
        exact hsupp.1 p (by simpa [b] using hpseg) hpclosed
      · intro w hw
        rw [Set.disjoint_left]
        intro p hpseg hpclosed
        exact (Set.disjoint_left.mp (hρ_vertex_disjoint w hw))
          (hseg_ball (by simpa [b] using hpseg)) hpclosed
      · intro x
        rw [Set.disjoint_left]
        intro p hpseg hpclosed
        exact (Set.disjoint_left.mp (hρ_intersection_disjoint x))
          (hseg_ball (by simpa [b] using hpseg)) hpclosed
    · let η : ℝ := min ρ εt
      have hη_pos : 0 < η := lt_min hρ_pos hεt_pos
      have hη_le_ρ : η ≤ ρ := min_le_left _ _
      have hη_le_εt : η ≤ εt := min_le_right _ _
      rcases target_halfspace.2 x η hx_rel hx_sphere hx_carrier hη_pos with
        ⟨u, hu_source, hu_target, hb_ballη, hhalfspace⟩
      let b : EuclideanSpace ℝ (Fin 2) :=
        residualPieceData.edgeParam (residualPieceData.owner i) u
      have hb_ballρ : b ∈ Metric.ball (residualPieceData.target i) ρ := by
        rw [Metric.mem_ball] at hb_ballη ⊢
        exact lt_of_lt_of_le (by simpa [b] using hb_ballη) hη_le_ρ
      have hb_ballεt :
          b ∈ Metric.ball (residualPieceData.target i) εt := by
        rw [Metric.mem_ball] at hb_ballη ⊢
        exact lt_of_lt_of_le (by simpa [b] using hb_ballη) hη_le_εt
      have hm_lt_u : m < u := htarget_ball_right u hu_source
        (by simpa [b] using hb_ballεt)
      have htarget_ball :
          residualPieceData.target i ∈
            Metric.ball (residualPieceData.target i) ρ := by
        rw [Metric.mem_ball, dist_self]
        exact hρ_pos
      have hseg_ball :
          segment ℝ (residualPieceData.target i) b ⊆
            Metric.ball (residualPieceData.target i) ρ :=
        (convex_ball (residualPieceData.target i) ρ).segment_subset
          htarget_ball hb_ballρ
      have hb_tube : b ∈ tube i := hρ_tube hb_ballρ
      have hseg_tube :
          segment ℝ (residualPieceData.target i) b ⊆ tube i := by
        intro p hp
        exact hρ_tube (hseg_ball hp)
      have hsupp :=
        PolygonalReplacementCircularEndpointSupportingHalfspace
          (le_of_lt (controlDisks.intersectionRadius_pos x)) hx_sphere
          (by simpa [b] using hhalfspace)
      refine ⟨u, hm_lt_u, hu_target, Or.inr ?_⟩
      refine ⟨x, hx_rel, hx_sphere, hx_carrier, ?_⟩
      dsimp only
      refine ⟨by simpa [b] using hb_tube, by simpa [b] using hseg_tube,
        ?_, by simpa [b] using hsupp.2, ?_, ?_⟩
      · intro p hpseg hpclosed
        exact hsupp.1 p (by simpa [b] using hpseg) hpclosed
      · intro v
        rw [Set.disjoint_left]
        intro p hpseg hpclosed
        exact (Set.disjoint_left.mp (hρ_vertex_disjoint v))
          (hseg_ball (by simpa [b] using hpseg)) hpclosed
      · intro y hy
        rw [Set.disjoint_left]
        intro p hpseg hpclosed
        exact (Set.disjoint_left.mp (hρ_intersection_disjoint y hy))
          (hseg_ball (by simpa [b] using hpseg)) hpclosed
  rcases source_pack with ⟨us, hsource_us, hus_m, hsource_good⟩
  rcases target_pack with ⟨ut, hm_ut, hut_target, htarget_good⟩
  exact ⟨us, ut, hsource_us, lt_trans hus_m hm_ut, hut_target,
    hsource_good, htarget_good⟩
