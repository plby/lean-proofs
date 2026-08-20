import ErdosProblems.Erdos733.ST.PolygonalReplacementCircularSourceEndpointChordControlFromHalfspace
import ErdosProblems.Erdos733.ST.PolygonalReplacementCircularSourceRetainedHalfspacePoint

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementCircularSourceEndpointChordControl]
lemma PolygonalReplacementCircularSourceEndpointChordControl {V : Type u}
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
-- BODY
  classical
  have halfspace_points :=
    PolygonalReplacementCircularSourceRetainedHalfspacePoint G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData i hcircular
  exact
    PolygonalReplacementCircularSourceEndpointChordControlFromHalfspace G D
      controlDisks boundaryPoints edgeEndpoints residualPieceData tube tube_open
      originalPiece_subset_tube i halfspace_points.1 halfspace_points.2

