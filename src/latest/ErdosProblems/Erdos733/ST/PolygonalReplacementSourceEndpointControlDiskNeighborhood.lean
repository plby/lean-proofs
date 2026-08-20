import ErdosProblems.Erdos733.ST.PolygonalReplacementControlDiskData
import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualPieceData

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementSourceEndpointControlDiskNeighborhood]
lemma PolygonalReplacementSourceEndpointControlDiskNeighborhood {V : Type u}
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
    (i : residualPieceData.pieceIndex) :
    (∃ v : V,
        v ∈ (residualPieceData.owner i).1 ∧
          residualPieceData.source i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
          residualPieceData.source i ∈
            D.edgeCarrier (residualPieceData.owner i) ∧
          ∃ ε : ℝ, 0 < ε ∧
            Metric.ball (residualPieceData.source i) ε ⊆ tube i ∧
            (∀ w : V, w ≠ v →
              Disjoint (Metric.ball (residualPieceData.source i) ε)
                (Metric.closedBall (D.vertexPlacement w)
                  (controlDisks.vertexRadius w))) ∧
            (∀ x : {p // p ∈ D.intersectionPoints},
              Disjoint (Metric.ball (residualPieceData.source i) ε)
                (Metric.closedBall x.1 (controlDisks.intersectionRadius x)))) ∨
      (∃ x : {p // p ∈ D.intersectionPoints},
        x.1 ∈ D.edgeRelativeInterior (residualPieceData.owner i) ∧
          residualPieceData.source i ∈
            Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
          residualPieceData.source i ∈
            D.edgeCarrier (residualPieceData.owner i) ∧
          ∃ ε : ℝ, 0 < ε ∧
            Metric.ball (residualPieceData.source i) ε ⊆ tube i ∧
            (∀ v : V,
              Disjoint (Metric.ball (residualPieceData.source i) ε)
                (Metric.closedBall (D.vertexPlacement v)
                  (controlDisks.vertexRadius v))) ∧
            (∀ y : {p // p ∈ D.intersectionPoints}, y ≠ x →
              Disjoint (Metric.ball (residualPieceData.source i) ε)
                (Metric.closedBall y.1 (controlDisks.intersectionRadius y)))) := by
-- BODY
  classical
  let s : EuclideanSpace ℝ (Fin 2) := residualPieceData.source i
  have hs_tube : s ∈ tube i := by
    exact originalPiece_subset_tube i (by simpa [s] using
      residualPieceData.source_mem_originalPiece i)
  rcases residualPieceData.source_on_control_boundary i with
    ⟨v, hv_owner, hv_sphere, hv_carrier⟩ |
    ⟨x, hx_rel, hx_sphere, hx_carrier⟩
  · have hs_assigned_closed :
        s ∈ Metric.closedBall (D.vertexPlacement v)
          (controlDisks.vertexRadius v) := by
      rw [Metric.mem_closedBall]
      exact le_of_eq (by
        rw [dist_eq_norm]
        simpa only [s, Metric.mem_sphere, dist_eq_norm] using hv_sphere)
    have hs_not_other_vertex :
        ∀ w : V, w ≠ v →
          s ∉ Metric.closedBall (D.vertexPlacement w)
            (controlDisks.vertexRadius w) := by
      intro w hw hs_w
      have hdisj :
          Disjoint
            (Metric.closedBall (D.vertexPlacement v)
              (controlDisks.vertexRadius v))
            (Metric.closedBall (D.vertexPlacement w)
              (controlDisks.vertexRadius w)) :=
        controlDisks.vertex_vertex_disjoint hw.symm
      exact (Set.disjoint_left.mp hdisj) hs_assigned_closed hs_w
    have hs_not_intersection :
        ∀ x : {p // p ∈ D.intersectionPoints},
          s ∉ Metric.closedBall x.1 (controlDisks.intersectionRadius x) := by
      intro x hs_x
      have hdisj :
          Disjoint
            (Metric.closedBall (D.vertexPlacement v)
              (controlDisks.vertexRadius v))
            (Metric.closedBall x.1 (controlDisks.intersectionRadius x)) :=
        controlDisks.vertex_intersection_disjoint v x
      exact (Set.disjoint_left.mp hdisj) hs_assigned_closed hs_x
    let safe : Set (EuclideanSpace ℝ (Fin 2)) :=
      tube i ∩
        (⋂ w : {w : V // w ≠ v},
          (Metric.closedBall (D.vertexPlacement w.1)
            (controlDisks.vertexRadius w.1))ᶜ) ∩
        (⋂ x : {p // p ∈ D.intersectionPoints},
          (Metric.closedBall x.1 (controlDisks.intersectionRadius x))ᶜ)
    have safe_open : IsOpen safe := by
      dsimp [safe]
      exact ((tube_open i).inter
        (isOpen_iInter_of_finite fun w =>
          Metric.isClosed_closedBall.isOpen_compl)).inter
        (isOpen_iInter_of_finite fun x =>
          Metric.isClosed_closedBall.isOpen_compl)
    have hs_safe : s ∈ safe := by
      dsimp [safe]
      refine ⟨⟨hs_tube, ?_⟩, ?_⟩
      · intro _ hmem
        rcases hmem with ⟨w, rfl⟩
        exact hs_not_other_vertex w.1 w.2
      · intro _ hmem
        rcases hmem with ⟨x, rfl⟩
        exact hs_not_intersection x
    rcases Metric.isOpen_iff.mp safe_open s hs_safe with
      ⟨ε, hεpos, hεsubset⟩
    left
    refine ⟨v, hv_owner, hv_sphere, hv_carrier, ε, hεpos, ?_, ?_, ?_⟩
    · intro p hp
      exact (hεsubset hp).1.1
    · intro w hw
      rw [Set.disjoint_left]
      intro p hp hpw
      exact
        ((hεsubset hp).1.2
          ((Metric.closedBall (D.vertexPlacement w)
            (controlDisks.vertexRadius w))ᶜ)
          ⟨⟨w, hw⟩, rfl⟩) hpw
    · intro x
      rw [Set.disjoint_left]
      intro p hp hpx
      exact
        ((hεsubset hp).2
          ((Metric.closedBall x.1 (controlDisks.intersectionRadius x))ᶜ)
          ⟨x, rfl⟩) hpx
  · have hs_assigned_closed :
        s ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) := by
      rw [Metric.mem_closedBall]
      exact le_of_eq (by
        rw [dist_eq_norm]
        simpa only [s, Metric.mem_sphere, dist_eq_norm] using hx_sphere)
    have hs_not_vertex :
        ∀ v : V,
          s ∉ Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v) := by
      intro v hs_v
      have hdisj :
          Disjoint
            (Metric.closedBall (D.vertexPlacement v)
              (controlDisks.vertexRadius v))
            (Metric.closedBall x.1 (controlDisks.intersectionRadius x)) :=
        controlDisks.vertex_intersection_disjoint v x
      exact (Set.disjoint_left.mp hdisj) hs_v hs_assigned_closed
    have hs_not_other_intersection :
        ∀ y : {p // p ∈ D.intersectionPoints}, y ≠ x →
          s ∉ Metric.closedBall y.1 (controlDisks.intersectionRadius y) := by
      intro y hy hs_y
      have hdisj :
          Disjoint
            (Metric.closedBall x.1 (controlDisks.intersectionRadius x))
            (Metric.closedBall y.1 (controlDisks.intersectionRadius y)) :=
        controlDisks.intersection_intersection_disjoint hy.symm
      exact (Set.disjoint_left.mp hdisj) hs_assigned_closed hs_y
    let safe : Set (EuclideanSpace ℝ (Fin 2)) :=
      tube i ∩
        (⋂ v : V,
          (Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v))ᶜ) ∩
        (⋂ y : {y : {p // p ∈ D.intersectionPoints} // y ≠ x},
          (Metric.closedBall y.1.1
            (controlDisks.intersectionRadius y.1))ᶜ)
    have safe_open : IsOpen safe := by
      dsimp [safe]
      exact ((tube_open i).inter
        (isOpen_iInter_of_finite fun v =>
          Metric.isClosed_closedBall.isOpen_compl)).inter
        (isOpen_iInter_of_finite fun y =>
          Metric.isClosed_closedBall.isOpen_compl)
    have hs_safe : s ∈ safe := by
      dsimp [safe]
      refine ⟨⟨hs_tube, ?_⟩, ?_⟩
      · intro _ hmem
        rcases hmem with ⟨v, rfl⟩
        exact hs_not_vertex v
      · intro _ hmem
        rcases hmem with ⟨y, rfl⟩
        exact hs_not_other_intersection y.1 y.2
    rcases Metric.isOpen_iff.mp safe_open s hs_safe with
      ⟨ε, hεpos, hεsubset⟩
    right
    refine ⟨x, hx_rel, hx_sphere, hx_carrier, ε, hεpos, ?_, ?_, ?_⟩
    · intro p hp
      exact (hεsubset hp).1.1
    · intro v
      rw [Set.disjoint_left]
      intro p hp hpv
      exact
        ((hεsubset hp).1.2
          ((Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v))ᶜ)
          ⟨v, rfl⟩) hpv
    · intro y hy
      rw [Set.disjoint_left]
      intro p hp hpy
      exact
        ((hεsubset hp).2
          ((Metric.closedBall y.1 (controlDisks.intersectionRadius y))ᶜ)
          ⟨⟨y, hy⟩, rfl⟩) hpy
