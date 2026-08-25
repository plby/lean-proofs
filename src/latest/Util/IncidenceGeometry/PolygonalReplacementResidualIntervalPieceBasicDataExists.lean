import Util.IncidenceGeometry.PolygonalReplacementResidualIntervalPieceBasicData
import Util.IncidenceGeometry.PolygonalReplacementResidualPieceSkeletonParameterBounds

open Classical
noncomputable section

universe u

lemma PolygonalReplacementResidualIntervalPieceBasicDataExists {V : Type u}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (edgeParam :
      (e : G.edgeFinset) → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (edgeParam_spec :
      ∀ e,
        Continuous (edgeParam e) ∧ Function.Injective (edgeParam e) ∧
          edgeParam e ⟨0, by simp⟩ = D.edgeSource e ∧
            edgeParam e ⟨1, by simp⟩ = D.edgeTarget e ∧
              D.edgeCarrier e = Set.range (edgeParam e) ∧
                D.edgeRelativeInterior e =
                  Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                    edgeParam e
                      ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩))
    (sourceBoundaryParam targetBoundaryParam :
      G.edgeFinset → Set.Icc (0 : ℝ) 1)
    (sourceBoundaryParam_eq :
      ∀ e, edgeParam e (sourceBoundaryParam e) =
        edgeEndpoints.sourceBoundaryPoint e)
    (targetBoundaryParam_eq :
      ∀ e, edgeParam e (targetBoundaryParam e) =
        edgeEndpoints.targetBoundaryPoint e)
    (sourceBoundaryParam_lt_targetBoundaryParam :
      ∀ e, sourceBoundaryParam e < targetBoundaryParam e)
    (intersectionCenterParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (intersectionCenterParam_eq :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          edgeParam e (intersectionCenterParam hx) = x.1)
    (intersectionCenterParam_interior :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          0 < (intersectionCenterParam hx).1 ∧
            (intersectionCenterParam hx).1 < 1)
    (intersectionLeftParam intersectionRightParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (S : PolygonalReplacementResidualPieceSkeletonData G D
      sourceBoundaryParam targetBoundaryParam intersectionCenterParam
      intersectionLeftParam intersectionRightParam) :
    Nonempty
      (PolygonalReplacementResidualIntervalPieceBasicData G D controlDisks
        boundaryPoints edgeEndpoints) := by
  classical
  have parameter_bounds :=
    PolygonalReplacementResidualPieceSkeletonParameterBounds G
      sourceBoundaryParam targetBoundaryParam S
  refine ⟨
    { pieceIndex := S.pieceIndex
      pieceIndex_fintype := S.pieceIndex_fintype
      owner := S.owner
      originalPiece := fun i =>
        edgeParam (S.owner i) '' Set.Icc (S.sourceParam i) (S.targetParam i)
      source := fun i => edgeParam (S.owner i) (S.sourceParam i)
      target := fun i => edgeParam (S.owner i) (S.targetParam i)
      edgeParam := edgeParam
      edgeParam_spec := edgeParam_spec
      sourceBoundaryParam := sourceBoundaryParam
      targetBoundaryParam := targetBoundaryParam
      sourceBoundaryParam_eq := sourceBoundaryParam_eq
      targetBoundaryParam_eq := targetBoundaryParam_eq
      sourceBoundaryParam_lt_targetBoundaryParam :=
        sourceBoundaryParam_lt_targetBoundaryParam
      sourceParam := S.sourceParam
      targetParam := S.targetParam
      sourceParam_lt_targetParam := S.sourceParam_lt_targetParam
      source_eq_edgeParam := ?_
      target_eq_edgeParam := ?_
      sourceBoundaryParam_le_sourceParam := parameter_bounds.1
      targetParam_le_targetBoundaryParam := parameter_bounds.2
      originalPiece_eq_parameter_interval := ?_
      intersectionCenterParam := intersectionCenterParam
      intersectionCenterParam_eq := intersectionCenterParam_eq
      intersectionCenterParam_interior := intersectionCenterParam_interior
      edgePieceOrder := S.edgePieceOrder
      edgePieceOrder_nonempty := S.edgePieceOrder_nonempty
      edgePieceOrder_nodup := S.edgePieceOrder_nodup
      edgePieceOrder_owner_iff := S.edgePieceOrder_owner_iff
      edgePieceOrder_first_sourceParam := S.edgePieceOrder_first_sourceParam
      edgePieceOrder_last_targetParam := S.edgePieceOrder_last_targetParam
      edgePieceOrder_consecutive_param_order :=
        S.edgePieceOrder_consecutive_param_order
      originalPiece_compact := ?_
      originalPiece_subset_owner := ?_
      source_mem_originalPiece := ?_
      target_mem_originalPiece := ?_
      source_ne_target := ?_ }⟩
  · intro i
    rfl
  · intro i
    rfl
  · intro i
    rfl
  · intro i
    exact isCompact_Icc.image (edgeParam_spec (S.owner i)).1
  · intro i p hp
    rcases hp with ⟨u, _hu, rfl⟩
    rcases edgeParam_spec (S.owner i) with
      ⟨_hcont, _hinj, _hsource, _htarget, hcarrier, _hrel⟩
    rw [hcarrier]
    exact ⟨u, rfl⟩
  · intro i
    refine ⟨S.sourceParam i, ?_, rfl⟩
    exact ⟨le_rfl, (S.sourceParam_lt_targetParam i).le⟩
  · intro i
    refine ⟨S.targetParam i, ?_, rfl⟩
    exact ⟨(S.sourceParam_lt_targetParam i).le, le_rfl⟩
  · intro i h
    have hinj : Function.Injective (edgeParam (S.owner i)) :=
      (edgeParam_spec (S.owner i)).2.1
    have hparam : S.sourceParam i = S.targetParam i := hinj h
    exact (ne_of_lt (S.sourceParam_lt_targetParam i)) hparam
