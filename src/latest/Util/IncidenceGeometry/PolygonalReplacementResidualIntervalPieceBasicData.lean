import Util.IncidenceGeometry.PolygonalReplacementEdgeBoundaryEndpointData

open Classical
noncomputable section

universe u

structure PolygonalReplacementResidualIntervalPieceBasicData {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints) where
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
  originalPiece_compact : ∀ i, IsCompact (originalPiece i)
  originalPiece_subset_owner : ∀ i, originalPiece i ⊆ D.edgeCarrier (owner i)
  source_mem_originalPiece : ∀ i, source i ∈ originalPiece i
  target_mem_originalPiece : ∀ i, target i ∈ originalPiece i
  source_ne_target : ∀ i, source i ≠ target i
