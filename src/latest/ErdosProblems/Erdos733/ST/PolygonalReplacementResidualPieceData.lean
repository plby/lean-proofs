import ErdosProblems.Erdos733.ST.PolygonalReplacementEdgeBoundaryEndpointData

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementResidualPieceData]
structure PolygonalReplacementResidualPieceData {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints) where
-- BODY
  pieceIndex : Type u
  pieceIndex_fintype : Fintype pieceIndex
  owner : pieceIndex → G.edgeFinset
  originalPiece : pieceIndex → Set (EuclideanSpace ℝ (Fin 2))
  source : pieceIndex → EuclideanSpace ℝ (Fin 2)
  target : pieceIndex → EuclideanSpace ℝ (Fin 2)
  edgeParam :
    (e : G.edgeFinset) → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)
  edgeParam_spec :
    ∀ e,
      Continuous (edgeParam e) ∧ Function.Injective (edgeParam e) ∧
        edgeParam e ⟨0, by simp⟩ = D.edgeSource e ∧
          edgeParam e ⟨1, by simp⟩ = D.edgeTarget e ∧
            D.edgeCarrier e = Set.range (edgeParam e) ∧
              D.edgeRelativeInterior e =
                Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                  edgeParam e
                    ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)
  sourceBoundaryParam : G.edgeFinset → Set.Icc (0 : ℝ) 1
  targetBoundaryParam : G.edgeFinset → Set.Icc (0 : ℝ) 1
  sourceBoundaryParam_eq :
    ∀ e, edgeParam e (sourceBoundaryParam e) =
      edgeEndpoints.sourceBoundaryPoint e
  targetBoundaryParam_eq :
    ∀ e, edgeParam e (targetBoundaryParam e) =
      edgeEndpoints.targetBoundaryPoint e
  sourceBoundaryParam_lt_targetBoundaryParam :
    ∀ e, sourceBoundaryParam e < targetBoundaryParam e
  sourceParam : pieceIndex → Set.Icc (0 : ℝ) 1
  targetParam : pieceIndex → Set.Icc (0 : ℝ) 1
  sourceParam_lt_targetParam : ∀ i, sourceParam i < targetParam i
  source_eq_edgeParam :
    ∀ i, source i = edgeParam (owner i) (sourceParam i)
  target_eq_edgeParam :
    ∀ i, target i = edgeParam (owner i) (targetParam i)
  sourceBoundaryParam_le_sourceParam :
    ∀ i, sourceBoundaryParam (owner i) ≤ sourceParam i
  targetParam_le_targetBoundaryParam :
    ∀ i, targetParam i ≤ targetBoundaryParam (owner i)
  originalPiece_eq_parameter_interval :
    ∀ i, originalPiece i =
      edgeParam (owner i) '' Set.Icc (sourceParam i) (targetParam i)
  intersectionCenterParam :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
      x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1
  intersectionCenterParam_eq :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
      (hx : x.1 ∈ D.edgeRelativeInterior e),
        edgeParam e (intersectionCenterParam hx) = x.1
  intersectionCenterParam_interior :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
      (hx : x.1 ∈ D.edgeRelativeInterior e),
        0 < (intersectionCenterParam hx).1 ∧
          (intersectionCenterParam hx).1 < 1
  intersectionLeftParam :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
      x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1
  intersectionRightParam :
    ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
      x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1
  edgePieceOrder : G.edgeFinset → List pieceIndex
  edgePieceOrder_nonempty : ∀ e, (edgePieceOrder e).length ≠ 0
  edgePieceOrder_nodup : ∀ e, (edgePieceOrder e).Nodup
  edgePieceOrder_owner_iff :
    ∀ e i, i ∈ edgePieceOrder e ↔ owner i = e
  edgePieceOrder_first_sourceParam :
    ∀ e i,
      (edgePieceOrder e).head? = some i →
        sourceParam i = sourceBoundaryParam e
  edgePieceOrder_last_targetParam :
    ∀ e i,
      (edgePieceOrder e).getLast? = some i →
        targetParam i = targetBoundaryParam e
  edgePieceOrder_consecutive_param_order :
    ∀ e n (hn : n + 1 < (edgePieceOrder e).length),
      targetParam ((edgePieceOrder e)[n]) <
        sourceParam ((edgePieceOrder e)[n + 1])
  edgePieceOrder_consecutive_intersection_cut_eq :
    ∀ e n (hn : n + 1 < (edgePieceOrder e).length),
      ∃ x : {p // p ∈ D.intersectionPoints},
        ∃ hx : x.1 ∈ D.edgeRelativeInterior e,
          target ((edgePieceOrder e)[n]) =
              edgeParam e (intersectionLeftParam hx) ∧
            source ((edgePieceOrder e)[n + 1]) =
                edgeParam e (intersectionRightParam hx) ∧
              targetParam ((edgePieceOrder e)[n]) =
                  intersectionLeftParam hx ∧
                sourceParam ((edgePieceOrder e)[n + 1]) =
                    intersectionRightParam hx ∧
                  intersectionLeftParam hx < intersectionCenterParam hx ∧
                    intersectionCenterParam hx < intersectionRightParam hx
  edgePieceOrder_consecutive_intersection_parameter_order :
    ∀ e n (hn : n + 1 < (edgePieceOrder e).length),
      ∃ x : {p // p ∈ D.intersectionPoints},
        ∃ hx : x.1 ∈ D.edgeRelativeInterior e,
          target ((edgePieceOrder e)[n]) ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
            source ((edgePieceOrder e)[n + 1]) ∈
                Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              targetParam ((edgePieceOrder e)[n]) <
                  intersectionCenterParam hx ∧
                intersectionCenterParam hx <
                  sourceParam ((edgePieceOrder e)[n + 1])
  edgePieceOrder_intersection_between_parameter_order :
    ∀ (x : {p // p ∈ D.intersectionPoints}) (e : G.edgeFinset)
      (hx : x.1 ∈ D.edgeRelativeInterior e),
        ∃ n, ∃ hn : n + 1 < (edgePieceOrder e).length,
          targetParam ((edgePieceOrder e)[n]) <
              intersectionCenterParam hx ∧
            intersectionCenterParam hx <
              sourceParam ((edgePieceOrder e)[n + 1])
  edgePieceOrder_first_source_boundary :
    ∀ e i,
      (edgePieceOrder e).head? = some i →
        source i = edgeEndpoints.sourceBoundaryPoint e ∧
          source i ∈
              Metric.sphere (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
                (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) ∧
            source i ∈ D.edgeCarrier e
  edgePieceOrder_last_target_boundary :
    ∀ e i,
      (edgePieceOrder e).getLast? = some i →
        target i = edgeEndpoints.targetBoundaryPoint e ∧
          target i ∈
              Metric.sphere (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
                (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) ∧
            target i ∈ D.edgeCarrier e
  edgePieceOrder_consecutive_intersection :
    ∀ e n (hn : n + 1 < (edgePieceOrder e).length),
      ∃ x : {p // p ∈ D.intersectionPoints},
        x.1 ∈ D.edgeRelativeInterior e ∧
          target ((edgePieceOrder e)[n]) ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
            target ((edgePieceOrder e)[n]) ∈ D.edgeCarrier e ∧
              source ((edgePieceOrder e)[n + 1]) ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                source ((edgePieceOrder e)[n + 1]) ∈ D.edgeCarrier e ∧
                  target ((edgePieceOrder e)[n]) ≠
                    source ((edgePieceOrder e)[n + 1])
  edgePieceOrder_intersection_between :
    ∀ (x : {p // p ∈ D.intersectionPoints}) (e : G.edgeFinset),
      x.1 ∈ D.edgeRelativeInterior e →
        ∃ n, ∃ hn : n + 1 < (edgePieceOrder e).length,
          target ((edgePieceOrder e)[n]) ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
            target ((edgePieceOrder e)[n]) ∈ D.edgeCarrier e ∧
              source ((edgePieceOrder e)[n + 1]) ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                source ((edgePieceOrder e)[n + 1]) ∈ D.edgeCarrier e ∧
                  target ((edgePieceOrder e)[n]) ≠
                    source ((edgePieceOrder e)[n + 1])
  originalPiece_compact : ∀ i, IsCompact (originalPiece i)
  originalPiece_subset_owner : ∀ i, originalPiece i ⊆ D.edgeCarrier (owner i)
  source_mem_originalPiece : ∀ i, source i ∈ originalPiece i
  target_mem_originalPiece : ∀ i, target i ∈ originalPiece i
  source_ne_target : ∀ i, source i ≠ target i
  source_on_control_boundary :
    ∀ i,
      (∃ v : V,
        v ∈ (owner i).1 ∧
          source i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
            source i ∈ D.edgeCarrier (owner i)) ∨
        (∃ x : {p // p ∈ D.intersectionPoints},
          x.1 ∈ D.edgeRelativeInterior (owner i) ∧
            source i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              source i ∈ D.edgeCarrier (owner i))
  target_on_control_boundary :
    ∀ i,
      (∃ v : V,
        v ∈ (owner i).1 ∧
          target i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
            target i ∈ D.edgeCarrier (owner i)) ∨
        (∃ x : {p // p ∈ D.intersectionPoints},
          x.1 ∈ D.edgeRelativeInterior (owner i) ∧
            target i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              target i ∈ D.edgeCarrier (owner i))
  source_endpoint_order :
    ∀ i,
      (sourceParam i = sourceBoundaryParam (owner i) ∧
        source i = edgeEndpoints.sourceBoundaryPoint (owner i) ∧
        source i ∈
          Metric.sphere
            (D.vertexPlacement (edgeEndpoints.edgeSourceVertex (owner i)))
            (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex (owner i))) ∧
        source i ∈ D.edgeCarrier (owner i)) ∨
        (∃ x : {p // p ∈ D.intersectionPoints},
          ∃ hx : x.1 ∈ D.edgeRelativeInterior (owner i),
            source i = edgeParam (owner i) (intersectionRightParam hx) ∧
              sourceParam i = intersectionRightParam hx ∧
              intersectionCenterParam hx < sourceParam i ∧
              source i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              source i ∈ D.edgeCarrier (owner i))
  target_endpoint_order :
    ∀ i,
      (targetParam i = targetBoundaryParam (owner i) ∧
        target i = edgeEndpoints.targetBoundaryPoint (owner i) ∧
        target i ∈
          Metric.sphere
            (D.vertexPlacement (edgeEndpoints.edgeTargetVertex (owner i)))
            (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex (owner i))) ∧
        target i ∈ D.edgeCarrier (owner i)) ∨
        (∃ x : {p // p ∈ D.intersectionPoints},
          ∃ hx : x.1 ∈ D.edgeRelativeInterior (owner i),
            target i = edgeParam (owner i) (intersectionLeftParam hx) ∧
              targetParam i = intersectionLeftParam hx ∧
              targetParam i < intersectionCenterParam hx ∧
              target i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              target i ∈ D.edgeCarrier (owner i))
  remaining_arc_covered :
    ∀ ⦃e p⦄,
      p ∈ D.edgeCarrier e →
        (∀ v : V,
          p ∉ Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v)) →
          (∀ x : {q // q ∈ D.intersectionPoints},
            p ∉ Metric.ball x.1 (controlDisks.intersectionRadius x)) →
            ∃ i : pieceIndex, owner i = e ∧ p ∈ originalPiece i
  vertex_boundary_attached :
    ∀ ⦃v e p⦄,
      v ∈ e.1 →
        p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
          p ∈ D.edgeCarrier e →
            ∃! i : pieceIndex, owner i = e ∧ (source i = p ∨ target i = p)
  intersection_boundary_attached :
    ∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e p⦄,
      x.1 ∈ D.edgeRelativeInterior e →
        p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
          p ∈ D.edgeCarrier e →
            ∃! i : pieceIndex, owner i = e ∧ (source i = p ∨ target i = p)
  originalPiece_avoids_vertex_disk_interiors :
    ∀ i v,
      Disjoint (originalPiece i)
        (Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v))
  originalPiece_avoids_intersection_disk_interiors :
    ∀ i (x : {p // p ∈ D.intersectionPoints}),
      Disjoint (originalPiece i)
        (Metric.ball x.1 (controlDisks.intersectionRadius x))
  originalPieces_pairwise_disjoint :
    ∀ ⦃i j⦄, i ≠ j → Disjoint (originalPiece i) (originalPiece j)
