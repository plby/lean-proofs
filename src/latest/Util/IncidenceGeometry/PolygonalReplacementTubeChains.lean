import Util.IncidenceGeometry.PolygonalReplacementTubeChainData
import Util.IncidenceGeometry.PolygonalReplacementBoundaryPointDataExists
import Util.IncidenceGeometry.PolygonalReplacementBoundaryPointParametersExist
import Util.IncidenceGeometry.PolygonalReplacementEdgeBoundaryEndpointDataExists
import Util.IncidenceGeometry.PolygonalReplacementEndpointBoundaryParamOrder
import Util.IncidenceGeometry.PolygonalReplacementEndpointDeletedIntervals
import Util.IncidenceGeometry.PolygonalReplacementIntersectionCenterEndpointParamOrder
import Util.IncidenceGeometry.PolygonalReplacementIntersectionDiskCutOrder
import Util.IncidenceGeometry.PolygonalReplacementIntersectionCutOpenBallIff
import Util.IncidenceGeometry.PolygonalReplacementPerEdgeCutSequence
import Util.IncidenceGeometry.PolygonalReplacementRetainedParameterIntervals
import Util.IncidenceGeometry.PolygonalReplacementStraightSegmentDisjointCutOrder
import Util.IncidenceGeometry.PolygonalReplacementResidualPieceSkeleton
import Util.IncidenceGeometry.PolygonalReplacementResidualIntervalPieceBasicDataExists
import Util.IncidenceGeometry.PolygonalReplacementResidualIntervalPieceControlComplement
import Util.IncidenceGeometry.PolygonalReplacementResidualPieceDataExists
import Util.IncidenceGeometry.PolygonalReplacementResidualPieceTubeNeighborhoods
import Util.IncidenceGeometry.PolygonalReplacementStraightResidualPieceChainInTube
import Util.IncidenceGeometry.PolygonalReplacementCircularResidualPieceChainInTube
import Util.IncidenceGeometry.PolygonalReplacementCircularResidualPieceCircleData
import Util.IncidenceGeometry.PolygonalReplacementCircularEndpointSupportingHalfspace
import Util.IncidenceGeometry.PolygonalReplacementCircleOutsideNearSupportingCoordinate
import Util.IncidenceGeometry.PolygonalReplacementSourceEndpointControlDiskNeighborhood
import Util.IncidenceGeometry.PolygonalReplacementCircularSourceEndpointChordControlFromHalfspace
import Util.IncidenceGeometry.PolygonalReplacementCircularSourceRetainedPoint
import Util.IncidenceGeometry.PolygonalReplacementCircularSourceEndpointCenterOrder
import Util.IncidenceGeometry.PolygonalReplacementCircularSourceRetainedHalfspacePoint
import Util.IncidenceGeometry.PolygonalReplacementCircularSourceEndpointChordControl
import Util.IncidenceGeometry.PolygonalReplacementCircularTargetRetainedPoint
import Util.IncidenceGeometry.PolygonalReplacementCircularTargetEndpointCenterOrder
import Util.IncidenceGeometry.PolygonalReplacementTargetEndpointControlDiskNeighborhood
import Util.IncidenceGeometry.PolygonalReplacementCircularTargetRetainedHalfspacePoint
import Util.IncidenceGeometry.PolygonalReplacementCircularTargetEndpointChordControlFromHalfspace
import Util.IncidenceGeometry.PolygonalReplacementCircularTargetEndpointChordControl
import Util.IncidenceGeometry.PolygonalReplacementCircularEndpointChordPair
import Util.IncidenceGeometry.PolygonalReplacementResidualOriginalPieceClosedBallContactOnlyEndpoint
import Util.IncidenceGeometry.PolygonalReplacementCircularMiddleSubarcSafeInTube
import Util.IncidenceGeometry.PolygonalReplacementCircularMiddleSubarcFiniteSafeConvexCover
import Util.IncidenceGeometry.PolygonalReplacementCircularMiddleSubarcSampledBySafeCover
import Util.IncidenceGeometry.CircleLineNoThreePoints
import Util.IncidenceGeometry.CircularOrderedSamplesBasicChordControls
import Util.IncidenceGeometry.CircularOrderedSamplesNonadjacentChordInteriors
import Util.IncidenceGeometry.PolygonalArcFromCircularOrderedSamples
import Mathlib.Data.Fintype.EquivFin

open Classical
noncomputable section

lemma PolygonalReplacementTubeChains {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D) :
    Nonempty (PolygonalReplacementTubeChainData G D controlDisks) := by
  obtain ⟨boundaryPoints⟩ :=
    PolygonalReplacementBoundaryPointDataExists G D controlDisks
  obtain ⟨edgeParam, edgeParam_spec, boundaryPoint_parameter_unique⟩ :=
    PolygonalReplacementBoundaryPointParametersExist G D controlDisks boundaryPoints
  obtain ⟨edgeBoundaryEndpoints⟩ :=
    PolygonalReplacementEdgeBoundaryEndpointDataExists G D controlDisks boundaryPoints
  have sourceBoundary_parameter_unique :
      ∀ e : G.edgeFinset,
        ∃! t : Set.Icc (0 : ℝ) 1,
          edgeParam e t = edgeBoundaryEndpoints.sourceBoundaryPoint e := by
    intro e
    have huniq := boundaryPoint_parameter_unique
      (edgeBoundaryEndpoints.sourceBoundaryIndex e)
    simpa [edgeBoundaryEndpoints.sourceBoundaryIndex_owner e,
      ← edgeBoundaryEndpoints.sourceBoundaryPoint_eq e] using huniq
  have targetBoundary_parameter_unique :
      ∀ e : G.edgeFinset,
        ∃! t : Set.Icc (0 : ℝ) 1,
          edgeParam e t = edgeBoundaryEndpoints.targetBoundaryPoint e := by
    intro e
    have huniq := boundaryPoint_parameter_unique
      (edgeBoundaryEndpoints.targetBoundaryIndex e)
    simpa [edgeBoundaryEndpoints.targetBoundaryIndex_owner e,
      ← edgeBoundaryEndpoints.targetBoundaryPoint_eq e] using huniq
  let sourceBoundaryParam : G.edgeFinset → Set.Icc (0 : ℝ) 1 := fun e =>
    Classical.choose (ExistsUnique.exists (sourceBoundary_parameter_unique e))
  let targetBoundaryParam : G.edgeFinset → Set.Icc (0 : ℝ) 1 := fun e =>
    Classical.choose (ExistsUnique.exists (targetBoundary_parameter_unique e))
  have sourceBoundaryParam_eq :
      ∀ e, edgeParam e (sourceBoundaryParam e) =
        edgeBoundaryEndpoints.sourceBoundaryPoint e := by
    intro e
    exact
      Classical.choose_spec
        (ExistsUnique.exists (sourceBoundary_parameter_unique e))
  have targetBoundaryParam_eq :
      ∀ e, edgeParam e (targetBoundaryParam e) =
        edgeBoundaryEndpoints.targetBoundaryPoint e := by
    intro e
    exact
      Classical.choose_spec
        (ExistsUnique.exists (targetBoundary_parameter_unique e))
  have endpoint_deleted_intervals :
      (∀ e, sourceBoundaryParam e < targetBoundaryParam e) ∧
        (∀ e (u : Set.Icc (0 : ℝ) 1), u ≤ sourceBoundaryParam e →
          edgeParam e u ∈
            Metric.closedBall
              (D.vertexPlacement (edgeBoundaryEndpoints.edgeSourceVertex e))
              (controlDisks.vertexRadius (edgeBoundaryEndpoints.edgeSourceVertex e))) ∧
        (∀ e (u : Set.Icc (0 : ℝ) 1), targetBoundaryParam e ≤ u →
          edgeParam e u ∈
            Metric.closedBall
              (D.vertexPlacement (edgeBoundaryEndpoints.edgeTargetVertex e))
              (controlDisks.vertexRadius (edgeBoundaryEndpoints.edgeTargetVertex e))) ∧
        (∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
          u ≤ targetBoundaryParam e →
            edgeParam e u ∉
              Metric.ball
                (D.vertexPlacement (edgeBoundaryEndpoints.edgeSourceVertex e))
                (controlDisks.vertexRadius (edgeBoundaryEndpoints.edgeSourceVertex e))) ∧
        (∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
          u ≤ targetBoundaryParam e →
            edgeParam e u ∉
              Metric.ball
                (D.vertexPlacement (edgeBoundaryEndpoints.edgeTargetVertex e))
                (controlDisks.vertexRadius (edgeBoundaryEndpoints.edgeTargetVertex e))) :=
    PolygonalReplacementEndpointDeletedIntervals G D controlDisks boundaryPoints
      edgeBoundaryEndpoints edgeParam edgeParam_spec sourceBoundaryParam
      targetBoundaryParam sourceBoundaryParam_eq targetBoundaryParam_eq
  have source_prefix_closed_vertexDisk :
      ∀ e (u : Set.Icc (0 : ℝ) 1), u ≤ sourceBoundaryParam e →
        edgeParam e u ∈
          Metric.closedBall
            (D.vertexPlacement (edgeBoundaryEndpoints.edgeSourceVertex e))
            (controlDisks.vertexRadius (edgeBoundaryEndpoints.edgeSourceVertex e)) :=
    endpoint_deleted_intervals.2.1
  have target_suffix_closed_vertexDisk :
      ∀ e (u : Set.Icc (0 : ℝ) 1), targetBoundaryParam e ≤ u →
        edgeParam e u ∈
          Metric.closedBall
            (D.vertexPlacement (edgeBoundaryEndpoints.edgeTargetVertex e))
            (controlDisks.vertexRadius (edgeBoundaryEndpoints.edgeTargetVertex e)) :=
    endpoint_deleted_intervals.2.2.1
  have middle_avoids_source_vertexDisk :
      ∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
        u ≤ targetBoundaryParam e →
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeBoundaryEndpoints.edgeSourceVertex e))
              (controlDisks.vertexRadius (edgeBoundaryEndpoints.edgeSourceVertex e)) :=
    endpoint_deleted_intervals.2.2.2.1
  have middle_avoids_target_vertexDisk :
      ∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
        u ≤ targetBoundaryParam e →
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeBoundaryEndpoints.edgeTargetVertex e))
              (controlDisks.vertexRadius (edgeBoundaryEndpoints.edgeTargetVertex e)) :=
    endpoint_deleted_intervals.2.2.2.2
  have intersectionCenterParam_exists :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e →
          ∃ t : Set.Icc (0 : ℝ) 1,
            edgeParam e t = x.1 ∧ 0 < t.1 ∧ t.1 < 1 := by
    intro x e hx
    rcases edgeParam_spec e with ⟨_hcont, _hinj, _hsource, _htarget,
      _hcarrier, hrel⟩
    rw [hrel] at hx
    rcases hx with ⟨t, ht⟩
    exact ⟨⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩, ht,
      t.2.1, t.2.2⟩
  let intersectionCenterParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1 := fun {x} {e} hx =>
    Classical.choose (intersectionCenterParam_exists (x := x) (e := e) hx)
  have intersectionCenterParam_eq :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          edgeParam e (intersectionCenterParam hx) = x.1 := by
    intro x e hx
    exact (Classical.choose_spec
      (intersectionCenterParam_exists (x := x) (e := e) hx)).1
  have intersectionCenterParam_interior :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          0 < (intersectionCenterParam hx).1 ∧
            (intersectionCenterParam hx).1 < 1 := by
    intro x e hx
    exact (Classical.choose_spec
      (intersectionCenterParam_exists (x := x) (e := e) hx)).2
  have endpointAndCenterParam_order :
      (∀ e, sourceBoundaryParam e < targetBoundaryParam e) ∧
        ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e),
            sourceBoundaryParam e < intersectionCenterParam hx ∧
              intersectionCenterParam hx < targetBoundaryParam e :=
    PolygonalReplacementIntersectionCenterEndpointParamOrder G D controlDisks
      boundaryPoints edgeBoundaryEndpoints edgeParam edgeParam_spec sourceBoundaryParam
      targetBoundaryParam sourceBoundaryParam_eq targetBoundaryParam_eq
      intersectionCenterParam intersectionCenterParam_eq
  have sourceBoundaryParam_lt_targetBoundaryParam :
      ∀ e, sourceBoundaryParam e < targetBoundaryParam e :=
    endpoint_deleted_intervals.1
  have intersectionCenterParam_between_endpoint_params :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          sourceBoundaryParam e < intersectionCenterParam hx ∧
            intersectionCenterParam hx < targetBoundaryParam e :=
    endpointAndCenterParam_order.2
  obtain ⟨intersectionLeftParam, intersectionRightParam,
      intersection_cut_order, intersection_cut_boundary,
      intersection_cut_boundary_exhaustive, intersection_cut_closedDisk,
      intersection_cut_ordered_by_centers⟩ :=
    PolygonalReplacementIntersectionDiskCutOrder G D controlDisks boundaryPoints
      edgeBoundaryEndpoints edgeParam edgeParam_spec boundaryPoint_parameter_unique
      sourceBoundaryParam targetBoundaryParam sourceBoundaryParam_eq
      targetBoundaryParam_eq intersectionCenterParam intersectionCenterParam_eq
      intersectionCenterParam_between_endpoint_params
  have perEdge_cut_sequences :=
    PolygonalReplacementPerEdgeCutSequence G D controlDisks boundaryPoints
      edgeBoundaryEndpoints edgeParam sourceBoundaryParam targetBoundaryParam
      sourceBoundaryParam_eq targetBoundaryParam_eq intersectionCenterParam
      intersectionCenterParam_eq intersectionCenterParam_between_endpoint_params
      intersectionLeftParam intersectionRightParam intersection_cut_order
      intersection_cut_closedDisk intersection_cut_ordered_by_centers
  have source_lt_intersectionLeft :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          sourceBoundaryParam e < intersectionLeftParam hx := by
    intro x e hx
    rcases perEdge_cut_sequences e with
      ⟨cuts, _cuts_nodup, cuts_mem, _center_strict, hsource_left,
        _hcut_order, _hright_target, _hconsec⟩
    exact hsource_left ⟨x, hx⟩ (cuts_mem ⟨x, hx⟩)
  have intersectionRight_lt_target :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          intersectionRightParam hx < targetBoundaryParam e := by
    intro x e hx
    rcases perEdge_cut_sequences e with
      ⟨cuts, _cuts_nodup, cuts_mem, _center_strict, _hsource_left,
        _hcut_order, hright_target, _hconsec⟩
    exact hright_target ⟨x, hx⟩ (cuts_mem ⟨x, hx⟩)
  have intersection_open_ball_iff_cut_interval :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e)
        (u : Set.Icc (0 : ℝ) 1),
          sourceBoundaryParam e ≤ u →
            u ≤ targetBoundaryParam e →
              (edgeParam e u ∈
                  Metric.ball x.1 (controlDisks.intersectionRadius x) ↔
                intersectionLeftParam hx < u ∧
                  u < intersectionRightParam hx) :=
    PolygonalReplacementIntersectionCutOpenBallIff G D controlDisks
      boundaryPoints edgeBoundaryEndpoints edgeParam edgeParam_spec
      sourceBoundaryParam targetBoundaryParam sourceBoundaryParam_eq
      targetBoundaryParam_eq intersectionCenterParam
      intersectionLeftParam intersectionRightParam intersection_cut_order
      intersection_cut_boundary intersection_cut_boundary_exhaustive
      intersection_cut_closedDisk
      source_lt_intersectionLeft intersectionRight_lt_target
  have retained_parameter_intervals :
      ∀ e : G.edgeFinset,
        ∃ cuts : List {x : {p // p ∈ D.intersectionPoints} //
            x.1 ∈ D.edgeRelativeInterior e},
          (cuts.Nodup ∧
            (∀ x : {x : {p // p ∈ D.intersectionPoints} //
                x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts) ∧
            (∀ i j (hi : i < cuts.length) (hj : j < cuts.length), i < j →
              intersectionCenterParam (cuts[i].2) <
                intersectionCenterParam (cuts[j].2)) ∧
            (∀ x : {x : {p // p ∈ D.intersectionPoints} //
                x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts →
              sourceBoundaryParam e < intersectionLeftParam x.2) ∧
            (∀ x : {x : {p // p ∈ D.intersectionPoints} //
                x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts →
              intersectionLeftParam x.2 < intersectionCenterParam x.2 ∧
                intersectionCenterParam x.2 < intersectionRightParam x.2) ∧
            (∀ x : {x : {p // p ∈ D.intersectionPoints} //
                x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts →
              intersectionRightParam x.2 < targetBoundaryParam e) ∧
            (∀ n (hn : n + 1 < cuts.length),
              intersectionRightParam (cuts[n].2) <
                intersectionLeftParam (cuts[n + 1].2)) ∧
            (∀ i j (hi : i < cuts.length) (hj : j < cuts.length), i < j →
              intersectionRightParam (cuts[i].2) <
                intersectionLeftParam (cuts[j].2))) ∧
          ∃ intervals :
              List (Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1),
            intervals.length = cuts.length + 1 ∧
              (∀ (n : ℕ) (a b : Set.Icc (0 : ℝ) 1),
                intervals[n]? = some (a, b) → a < b) ∧
              intervals.head?.map Prod.fst = some (sourceBoundaryParam e) ∧
              intervals.getLast?.map Prod.snd = some (targetBoundaryParam e) ∧
              (∀ (n : ℕ) (hn : n < cuts.length),
                intervals[n]?.map Prod.snd =
                    some (intersectionLeftParam (cuts[n].2)) ∧
                  intervals[n + 1]?.map Prod.fst =
                      some (intersectionRightParam (cuts[n].2)) ∧
                    intersectionLeftParam (cuts[n].2) <
                        intersectionCenterParam (cuts[n].2) ∧
                      intersectionCenterParam (cuts[n].2) <
                        intersectionRightParam (cuts[n].2)) := by
    intro e
    rcases perEdge_cut_sequences e with
      ⟨cuts, cuts_nodup, cuts_mem, center_strict, hsource_left,
        hcut_order, hright_target, hconsec⟩
    have cut_interval_order :
        ∀ i j (hi : i < cuts.length) (hj : j < cuts.length), i < j →
          intersectionRightParam (cuts[i].2) <
            intersectionLeftParam (cuts[j].2) := by
      intro i j hi hj hij
      have hcuts_ne : cuts[i] ≠ cuts[j] := by
        intro hcuts_eq
        have hidx : i = j := (List.Nodup.getElem_inj_iff cuts_nodup).mp hcuts_eq
        omega
      have hpoints_ne : (cuts[i]).1 ≠ (cuts[j]).1 := by
        intro hpoints_eq
        exact hcuts_ne (Subtype.ext hpoints_eq)
      exact intersection_cut_ordered_by_centers (cuts[i].2) (cuts[j].2)
        hpoints_ne (center_strict i j hi hj hij)
    refine ⟨cuts, ?_, ?_⟩
    · exact ⟨cuts_nodup, cuts_mem, center_strict, hsource_left, hcut_order,
        hright_target, hconsec, cut_interval_order⟩
    · exact
      PolygonalReplacementRetainedParameterIntervals
        (sourceBoundaryParam e) (targetBoundaryParam e) cuts
        (fun x => intersectionLeftParam x.2)
        (fun x => intersectionCenterParam x.2)
        (fun x => intersectionRightParam x.2)
        (sourceBoundaryParam_lt_targetBoundaryParam e)
        hsource_left hcut_order hright_target hconsec
  obtain ⟨residualPieceSkeleton⟩ :=
    PolygonalReplacementResidualPieceSkeleton G D sourceBoundaryParam
      targetBoundaryParam intersectionCenterParam intersectionLeftParam
      intersectionRightParam retained_parameter_intervals
  obtain ⟨residualPieceBasic,
      residualPiece_basic_cert,
      residualPiece_basic_avoids_vertex_disk_interiors,
      residualPiece_basic_avoids_intersection_disk_interiors,
      residualPiece_basic_remaining_arc_covered⟩ :=
    PolygonalReplacementResidualIntervalPieceControlComplement G D controlDisks
      boundaryPoints edgeBoundaryEndpoints edgeParam edgeParam_spec
      sourceBoundaryParam targetBoundaryParam sourceBoundaryParam_eq
      targetBoundaryParam_eq sourceBoundaryParam_lt_targetBoundaryParam
      source_prefix_closed_vertexDisk target_suffix_closed_vertexDisk
      middle_avoids_source_vertexDisk middle_avoids_target_vertexDisk
      intersectionCenterParam intersectionCenterParam_eq
      intersectionCenterParam_interior intersectionLeftParam
      intersectionRightParam intersection_open_ball_iff_cut_interval
      residualPieceSkeleton
  obtain ⟨residualPieceData⟩ :=
    PolygonalReplacementResidualPieceDataExists G D controlDisks
      boundaryPoints edgeBoundaryEndpoints edgeParam edgeParam_spec
      sourceBoundaryParam targetBoundaryParam sourceBoundaryParam_eq
      targetBoundaryParam_eq sourceBoundaryParam_lt_targetBoundaryParam
      intersectionCenterParam intersectionCenterParam_eq
      intersectionCenterParam_interior intersectionLeftParam
      intersectionRightParam intersection_cut_boundary
      intersection_cut_boundary_exhaustive residualPieceSkeleton
      residualPieceBasic residualPiece_basic_cert
      residualPiece_basic_avoids_vertex_disk_interiors
      residualPiece_basic_avoids_intersection_disk_interiors
      residualPiece_basic_remaining_arc_covered
  obtain ⟨tube, tube_open, originalPiece_subset_tube,
      tubes_pairwise_disjoint⟩ :=
    PolygonalReplacementResidualPieceTubeNeighborhoods G D controlDisks
      boundaryPoints edgeBoundaryEndpoints residualPieceData
  have straight_residual_piece_chain :=
    PolygonalReplacementStraightResidualPieceChainInTube G D controlDisks
      boundaryPoints edgeBoundaryEndpoints residualPieceData tube tube_open
      originalPiece_subset_tube
  have circular_residual_piece_chain :=
    PolygonalReplacementCircularResidualPieceChainInTube G D controlDisks
      boundaryPoints edgeBoundaryEndpoints residualPieceData tube tube_open
      originalPiece_subset_tube
  have chain_exists :
      ∀ i : residualPieceData.pieceIndex,
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
                    p ∈ Metric.closedBall x.1
                        (controlDisks.intersectionRadius x) →
                      (p = residualPieceData.source i ∧
                          residualPieceData.source i ∈
                            Metric.sphere x.1
                              (controlDisks.intersectionRadius x)) ∨
                        (p = residualPieceData.target i ∧
                          residualPieceData.target i ∈
                            Metric.sphere x.1
                              (controlDisks.intersectionRadius x))) := by
    intro i
    rcases D.edge_is_simple_lineSegment_or_circularArc
        (residualPieceData.owner i) with hstraight | hcircular
    · exact straight_residual_piece_chain i hstraight
    · rcases hcircular with ⟨c, r, γ, hcircular⟩
      exact circular_residual_piece_chain i (c := c) (r := r) (γ := γ)
        hcircular
  let pieceChain : residualPieceData.pieceIndex → PolygonalArc := fun i =>
    Classical.choose (chain_exists i)
  have chain_spec :
      ∀ i : residualPieceData.pieceIndex,
        (pieceChain i).source = residualPieceData.source i ∧
          (pieceChain i).target = residualPieceData.target i ∧
            (pieceChain i).carrier ⊆ tube i ∧
              (∀ v : V,
                Disjoint (pieceChain i).relativeInterior
                  (Metric.ball (D.vertexPlacement v)
                    (controlDisks.vertexRadius v))) ∧
              (∀ x : {p // p ∈ D.intersectionPoints},
                Disjoint (pieceChain i).relativeInterior
                  (Metric.ball x.1 (controlDisks.intersectionRadius x))) ∧
              (∀ v p,
                p ∈ (pieceChain i).carrier →
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
                p ∈ (pieceChain i).carrier →
                  p ∈ Metric.closedBall x.1
                      (controlDisks.intersectionRadius x) →
                    (p = residualPieceData.source i ∧
                        residualPieceData.source i ∈
                          Metric.sphere x.1
                            (controlDisks.intersectionRadius x)) ∨
                      (p = residualPieceData.target i ∧
                        residualPieceData.target i ∈
                          Metric.sphere x.1
                            (controlDisks.intersectionRadius x))) := by
    intro i
    exact Classical.choose_spec (chain_exists i)
  letI : Fintype residualPieceData.pieceIndex :=
    residualPieceData.pieceIndex_fintype
  let pieceEquiv :
      residualPieceData.pieceIndex ≃
        Fin (Fintype.card residualPieceData.pieceIndex) :=
    Fintype.equivFin residualPieceData.pieceIndex
  refine ⟨
    { pieceIndex := Fin (Fintype.card residualPieceData.pieceIndex)
      pieceIndex_fintype := inferInstance
      owner := fun i => residualPieceData.owner (pieceEquiv.symm i)
      originalPiece := fun i => residualPieceData.originalPiece (pieceEquiv.symm i)
      source := fun i => residualPieceData.source (pieceEquiv.symm i)
      target := fun i => residualPieceData.target (pieceEquiv.symm i)
      tube := fun i => tube (pieceEquiv.symm i)
      chain := fun i => pieceChain (pieceEquiv.symm i)
      edgeSourceVertex := edgeBoundaryEndpoints.edgeSourceVertex
      edgeTargetVertex := edgeBoundaryEndpoints.edgeTargetVertex
      edgeSourceVertex_mem := edgeBoundaryEndpoints.edgeSourceVertex_mem
      edgeTargetVertex_mem := edgeBoundaryEndpoints.edgeTargetVertex_mem
      edgeSource_eq_vertexPlacement :=
        edgeBoundaryEndpoints.edgeSource_eq_vertexPlacement
      edgeTarget_eq_vertexPlacement :=
        edgeBoundaryEndpoints.edgeTarget_eq_vertexPlacement
      edgePieceOrder := fun e => (residualPieceData.edgePieceOrder e).map pieceEquiv
      edgePieceOrder_nonempty := by
        intro e
        simpa using residualPieceData.edgePieceOrder_nonempty e
      edgePieceOrder_nodup := by
        intro e
        exact (residualPieceData.edgePieceOrder_nodup e).map pieceEquiv.injective
      edgePieceOrder_owner_iff := by
        intro e i
        constructor
        · intro hi
          rcases List.mem_map.mp hi with ⟨j, hj, hji⟩
          subst i
          simpa using (residualPieceData.edgePieceOrder_owner_iff e j).mp hj
        · intro hi
          have hmem :
              pieceEquiv.symm i ∈ residualPieceData.edgePieceOrder e := by
            exact
              (residualPieceData.edgePieceOrder_owner_iff e
                (pieceEquiv.symm i)).mpr hi
          exact List.mem_map.mpr
            ⟨pieceEquiv.symm i, hmem, by simp [pieceEquiv]⟩
      edgePieceOrder_first_source_boundary := by
        intro e i hi
        have hi_old :
            (residualPieceData.edgePieceOrder e).head? =
              some (pieceEquiv.symm i) := by
          rw [List.head?_map] at hi
          cases hhead : (residualPieceData.edgePieceOrder e).head? with
          | none =>
              simp [hhead] at hi
          | some j =>
              simp [hhead] at hi
              subst i
              simp [pieceEquiv]
        rcases residualPieceData.edgePieceOrder_first_source_boundary e
            (pieceEquiv.symm i) hi_old with
          ⟨_hsource, hsphere, hcarrier⟩
        exact ⟨hsphere, hcarrier⟩
      edgePieceOrder_last_target_boundary := by
        intro e i hi
        have hi_old :
            (residualPieceData.edgePieceOrder e).getLast? =
              some (pieceEquiv.symm i) := by
          rw [List.getLast?_map] at hi
          cases hlast : (residualPieceData.edgePieceOrder e).getLast? with
          | none =>
              simp [hlast] at hi
          | some j =>
              simp [hlast] at hi
              subst i
              simp [pieceEquiv]
        rcases residualPieceData.edgePieceOrder_last_target_boundary e
            (pieceEquiv.symm i) hi_old with
          ⟨_htarget, hsphere, hcarrier⟩
        exact ⟨hsphere, hcarrier⟩
      edgePieceOrder_consecutive_intersection := by
        intro e n hn
        have hn_old :
            n + 1 < (residualPieceData.edgePieceOrder e).length := by
          simpa using hn
        rcases residualPieceData.edgePieceOrder_consecutive_intersection e n
            hn_old with
          ⟨x, hxrel, htarget_sphere, htarget_carrier, hsource_sphere,
            hsource_carrier, hne⟩
        refine ⟨x, hxrel, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [List.getElem_map]
            using htarget_sphere
        · simpa [List.getElem_map]
            using htarget_carrier
        · simpa [List.getElem_map]
            using hsource_sphere
        · simpa [List.getElem_map]
            using hsource_carrier
        · simpa [List.getElem_map]
            using hne
      edgePieceOrder_intersection_between := by
        intro x e hxrel
        rcases residualPieceData.edgePieceOrder_intersection_between x e hxrel
          with
          ⟨n, hn_old, htarget_sphere, htarget_carrier, hsource_sphere,
            hsource_carrier, hne⟩
        refine ⟨n, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa using hn_old
        · simpa [List.getElem_map] using htarget_sphere
        · simpa [List.getElem_map] using htarget_carrier
        · simpa [List.getElem_map] using hsource_sphere
        · simpa [List.getElem_map] using hsource_carrier
        · simpa [List.getElem_map] using hne
      originalPiece_compact := by
        intro i
        exact residualPieceData.originalPiece_compact (pieceEquiv.symm i)
      originalPiece_subset_owner := by
        intro i p hp
        exact residualPieceData.originalPiece_subset_owner (pieceEquiv.symm i) hp
      source_mem_originalPiece := by
        intro i
        exact residualPieceData.source_mem_originalPiece (pieceEquiv.symm i)
      target_mem_originalPiece := by
        intro i
        exact residualPieceData.target_mem_originalPiece (pieceEquiv.symm i)
      source_ne_target := by
        intro i
        exact residualPieceData.source_ne_target (pieceEquiv.symm i)
      source_on_control_boundary := by
        intro i
        exact residualPieceData.source_on_control_boundary (pieceEquiv.symm i)
      target_on_control_boundary := by
        intro i
        exact residualPieceData.target_on_control_boundary (pieceEquiv.symm i)
      remaining_arc_covered := by
        intro e p hpCarrier hpVertex hpIntersection
        rcases residualPieceData.remaining_arc_covered hpCarrier hpVertex
            hpIntersection with
          ⟨i, hi_owner, hp_piece⟩
        exact ⟨pieceEquiv i, by simpa [pieceEquiv] using hi_owner,
          by simpa [pieceEquiv] using hp_piece⟩
      vertex_boundary_attached := by
        intro v e p hv hpSphere hpCarrier
        rcases residualPieceData.vertex_boundary_attached hv hpSphere
            hpCarrier with
          ⟨i, hi, huniq⟩
        refine ⟨pieceEquiv i, ?_, ?_⟩
        · simpa [pieceEquiv] using hi
        · intro j hj
          have hj_old :
              residualPieceData.owner (pieceEquiv.symm j) = e ∧
                (residualPieceData.source (pieceEquiv.symm j) = p ∨
                  residualPieceData.target (pieceEquiv.symm j) = p) := by
            simpa [pieceEquiv] using hj
          have hsymm : pieceEquiv.symm j = i :=
            huniq (pieceEquiv.symm j) hj_old
          calc
            j = pieceEquiv (pieceEquiv.symm j) := by
              exact (pieceEquiv.apply_symm_apply j).symm
            _ = pieceEquiv i := by rw [hsymm]
      intersection_boundary_attached := by
        intro x e p hx hpSphere hpCarrier
        rcases residualPieceData.intersection_boundary_attached hx hpSphere
            hpCarrier with
          ⟨i, hi, huniq⟩
        refine ⟨pieceEquiv i, ?_, ?_⟩
        · simpa [pieceEquiv] using hi
        · intro j hj
          have hj_old :
              residualPieceData.owner (pieceEquiv.symm j) = e ∧
                (residualPieceData.source (pieceEquiv.symm j) = p ∨
                  residualPieceData.target (pieceEquiv.symm j) = p) := by
            simpa [pieceEquiv] using hj
          have hsymm : pieceEquiv.symm j = i :=
            huniq (pieceEquiv.symm j) hj_old
          calc
            j = pieceEquiv (pieceEquiv.symm j) := by
              exact (pieceEquiv.apply_symm_apply j).symm
            _ = pieceEquiv i := by rw [hsymm]
      originalPiece_avoids_vertex_disk_interiors :=
        by
          intro i v
          exact
            residualPieceData.originalPiece_avoids_vertex_disk_interiors
              (pieceEquiv.symm i) v
      originalPiece_avoids_intersection_disk_interiors :=
        by
          intro i x
          exact
            residualPieceData.originalPiece_avoids_intersection_disk_interiors
              (pieceEquiv.symm i) x
      originalPieces_pairwise_disjoint := by
        intro i j hij
        have hij_old : pieceEquiv.symm i ≠ pieceEquiv.symm j := by
          intro h
          exact hij (by simpa [pieceEquiv] using congrArg pieceEquiv h)
        exact residualPieceData.originalPieces_pairwise_disjoint hij_old
      tube_open := by
        intro i
        exact tube_open (pieceEquiv.symm i)
      originalPiece_subset_tube := by
        intro i p hp
        exact originalPiece_subset_tube (pieceEquiv.symm i) hp
      chain_endpoints := by
        intro i
        exact ⟨(chain_spec (pieceEquiv.symm i)).1,
          (chain_spec (pieceEquiv.symm i)).2.1⟩
      chain_carrier_subset_tube := by
        intro i
        exact (chain_spec (pieceEquiv.symm i)).2.2.1
      chain_relativeInterior_avoids_vertex_disk_interiors := by
        intro i v
        exact (chain_spec (pieceEquiv.symm i)).2.2.2.1 v
      chain_relativeInterior_avoids_intersection_disk_interiors := by
        intro i x
        exact (chain_spec (pieceEquiv.symm i)).2.2.2.2.1 x
      chain_carrier_meets_vertex_closedBall_only_endpoint := by
        intro i v p hpCarrier hpClosed
        exact (chain_spec (pieceEquiv.symm i)).2.2.2.2.2.1 v p
          hpCarrier hpClosed
      chain_carrier_meets_intersection_closedBall_only_endpoint := by
        intro i x p hpCarrier hpClosed
        exact (chain_spec (pieceEquiv.symm i)).2.2.2.2.2.2 x p
          hpCarrier hpClosed
      tubes_pairwise_disjoint := by
        intro i j hij
        have hij_old : pieceEquiv.symm i ≠ pieceEquiv.symm j := by
          intro h
          exact hij (by simpa [pieceEquiv] using congrArg pieceEquiv h)
        exact tubes_pairwise_disjoint hij_old
      chain_carriers_pairwise_disjoint := by
        intro i j hij
        have hij_old : pieceEquiv.symm i ≠ pieceEquiv.symm j := by
          intro h
          exact hij (by simpa [pieceEquiv] using congrArg pieceEquiv h)
        rw [Set.disjoint_left]
        intro p hpi hpj
        exact
          (Set.disjoint_left.mp (tubes_pairwise_disjoint hij_old))
            ((chain_spec (pieceEquiv.symm i)).2.2.1 hpi)
            ((chain_spec (pieceEquiv.symm j)).2.2.1 hpj) }⟩
