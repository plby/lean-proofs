import Util.IncidenceGeometry.PolygonalReplacementResidualIntervalPieceBasicData
import Util.IncidenceGeometry.PolygonalReplacementResidualPieceSkeletonParameterBounds
import Util.IncidenceGeometry.PolygonalReplacementRetainedIntervalVertexDiskAvoidance
import Util.IncidenceGeometry.PolygonalReplacementRetainedIntervalIntersectionDiskComplement

open Classical
noncomputable section

universe u

lemma PolygonalReplacementResidualIntervalPieceControlComplement {V : Type u}
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
    (source_prefix_closed_vertexDisk :
      ∀ e (u : Set.Icc (0 : ℝ) 1), u ≤ sourceBoundaryParam e →
        edgeParam e u ∈
          Metric.closedBall
            (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
            (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)))
    (target_suffix_closed_vertexDisk :
      ∀ e (u : Set.Icc (0 : ℝ) 1), targetBoundaryParam e ≤ u →
        edgeParam e u ∈
          Metric.closedBall
            (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
            (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)))
    (middle_avoids_source_vertexDisk :
      ∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
        u ≤ targetBoundaryParam e →
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)))
    (middle_avoids_target_vertexDisk :
      ∀ e (u : Set.Icc (0 : ℝ) 1), sourceBoundaryParam e ≤ u →
        u ≤ targetBoundaryParam e →
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)))
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
    (intersection_open_ball_iff_cut_interval :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e)
        (u : Set.Icc (0 : ℝ) 1),
          sourceBoundaryParam e ≤ u →
            u ≤ targetBoundaryParam e →
              (edgeParam e u ∈
                  Metric.ball x.1 (controlDisks.intersectionRadius x) ↔
                intersectionLeftParam hx < u ∧
                  u < intersectionRightParam hx))
    (S : PolygonalReplacementResidualPieceSkeletonData G D
      sourceBoundaryParam targetBoundaryParam intersectionCenterParam
      intersectionLeftParam intersectionRightParam) :
    ∃ B : PolygonalReplacementResidualIntervalPieceBasicData G D controlDisks
        boundaryPoints edgeEndpoints,
      (∃ pieceEquiv : B.pieceIndex ≃ S.pieceIndex,
        (∀ i : B.pieceIndex, B.owner i = S.owner (pieceEquiv i)) ∧
        (∀ i : B.pieceIndex,
          B.sourceParam i = S.sourceParam (pieceEquiv i)) ∧
        (∀ i : B.pieceIndex,
          B.targetParam i = S.targetParam (pieceEquiv i)) ∧
        (∀ i : B.pieceIndex,
          B.source i =
            edgeParam (S.owner (pieceEquiv i))
              (S.sourceParam (pieceEquiv i))) ∧
        (∀ i : B.pieceIndex,
          B.target i =
            edgeParam (S.owner (pieceEquiv i))
              (S.targetParam (pieceEquiv i))) ∧
        (∀ i : B.pieceIndex,
          B.originalPiece i =
            edgeParam (S.owner (pieceEquiv i)) ''
              Set.Icc (S.sourceParam (pieceEquiv i))
                (S.targetParam (pieceEquiv i))) ∧
        (∀ e : G.edgeFinset,
          (B.edgePieceOrder e).map (fun i => pieceEquiv i) =
            S.edgePieceOrder e)) ∧
      (∀ i v,
        Disjoint (B.originalPiece i)
          (Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v))) ∧
      (∀ i (x : {p // p ∈ D.intersectionPoints}),
        Disjoint (B.originalPiece i)
          (Metric.ball x.1 (controlDisks.intersectionRadius x))) ∧
      (∀ ⦃e p⦄,
        p ∈ D.edgeCarrier e →
          (∀ v : V,
            p ∉ Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v)) →
            (∀ x : {q // q ∈ D.intersectionPoints},
              p ∉ Metric.ball x.1 (controlDisks.intersectionRadius x)) →
              ∃ i : B.pieceIndex, B.owner i = e ∧ p ∈ B.originalPiece i) := by
  classical
  have parameter_bounds :=
    PolygonalReplacementResidualPieceSkeletonParameterBounds G
      sourceBoundaryParam targetBoundaryParam S
  have retained_interval_skeleton_avoids_vertex_disks :
      ∀ i (u : Set.Icc (0 : ℝ) 1),
        S.sourceParam i ≤ u →
          u ≤ S.targetParam i →
            ∀ v : V,
              edgeParam (S.owner i) u ∉
                Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v) :=
    PolygonalReplacementRetainedIntervalVertexDiskAvoidance G D controlDisks
      boundaryPoints edgeEndpoints edgeParam edgeParam_spec
      sourceBoundaryParam targetBoundaryParam S
      middle_avoids_source_vertexDisk middle_avoids_target_vertexDisk
  have retained_interval_intersection_disk_complement :=
    PolygonalReplacementRetainedIntervalIntersectionDiskComplement G D
      controlDisks edgeParam edgeParam_spec sourceBoundaryParam
      targetBoundaryParam intersectionCenterParam intersectionLeftParam
      intersectionRightParam intersection_open_ball_iff_cut_interval S
  have retained_interval_skeleton_avoids_intersection_disks :
      ∀ i (u : Set.Icc (0 : ℝ) 1),
        S.sourceParam i ≤ u →
          u ≤ S.targetParam i →
            ∀ x : {q // q ∈ D.intersectionPoints},
              edgeParam (S.owner i) u ∉
                Metric.ball x.1 (controlDisks.intersectionRadius x) :=
    retained_interval_intersection_disk_complement.1
  have retained_interval_skeleton_intersection_disk_image_coverage :
      ∀ e (u : Set.Icc (0 : ℝ) 1),
        sourceBoundaryParam e ≤ u →
          u ≤ targetBoundaryParam e →
            (∀ x : {q // q ∈ D.intersectionPoints},
              edgeParam e u ∉
                Metric.ball x.1 (controlDisks.intersectionRadius x)) →
              ∃ i, S.owner i = e ∧
                edgeParam e u ∈
                  edgeParam (S.owner i) ''
                    Set.Icc (S.sourceParam i) (S.targetParam i) :=
    retained_interval_intersection_disk_complement.2.2.2
  let B : PolygonalReplacementResidualIntervalPieceBasicData G D controlDisks
      boundaryPoints edgeEndpoints :=
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
      source_eq_edgeParam := by
        intro i
        rfl
      target_eq_edgeParam := by
        intro i
        rfl
      sourceBoundaryParam_le_sourceParam := parameter_bounds.1
      targetParam_le_targetBoundaryParam := parameter_bounds.2
      originalPiece_eq_parameter_interval := by
        intro i
        rfl
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
      originalPiece_compact := by
        intro i
        exact isCompact_Icc.image (edgeParam_spec (S.owner i)).1
      originalPiece_subset_owner := by
        intro i p hp
        rcases hp with ⟨u, _hu, rfl⟩
        rcases edgeParam_spec (S.owner i) with
          ⟨_hcont, _hinj, _hsource, _htarget, hcarrier, _hrel⟩
        rw [hcarrier]
        exact ⟨u, rfl⟩
      source_mem_originalPiece := by
        intro i
        refine ⟨S.sourceParam i, ?_, rfl⟩
        exact ⟨le_rfl, (S.sourceParam_lt_targetParam i).le⟩
      target_mem_originalPiece := by
        intro i
        refine ⟨S.targetParam i, ?_, rfl⟩
        exact ⟨(S.sourceParam_lt_targetParam i).le, le_rfl⟩
      source_ne_target := by
        intro i h
        have hinj : Function.Injective (edgeParam (S.owner i)) :=
          (edgeParam_spec (S.owner i)).2.1
        have hparam : S.sourceParam i = S.targetParam i := hinj h
        exact (ne_of_lt (S.sourceParam_lt_targetParam i)) hparam }
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · refine ⟨Equiv.refl S.pieceIndex, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
    · intro i
      rfl
    · intro i
      rfl
    · intro i
      rfl
    · intro i
      rfl
    · intro e
      simp [B]
  · intro i v
    rw [Set.disjoint_left]
    intro p hp hball
    change p ∈ edgeParam (S.owner i) ''
      Set.Icc (S.sourceParam i) (S.targetParam i) at hp
    rcases hp with ⟨u, hu, rfl⟩
    exact retained_interval_skeleton_avoids_vertex_disks i u hu.1 hu.2 v hball
  · intro i x
    rw [Set.disjoint_left]
    intro p hp hball
    change p ∈ edgeParam (S.owner i) ''
      Set.Icc (S.sourceParam i) (S.targetParam i) at hp
    rcases hp with ⟨u, hu, rfl⟩
    exact
      retained_interval_skeleton_avoids_intersection_disks i u hu.1 hu.2 x hball
  · intro e p hp_carrier havoids_vertices havoids_intersections
    rcases edgeParam_spec e with
      ⟨_hcont, hinj, _hsource, _htarget, hcarrier, _hrel⟩
    rw [hcarrier] at hp_carrier
    rcases hp_carrier with ⟨u, rfl⟩
    have hp_on_carrier : edgeParam e u ∈ D.edgeCarrier e := by
      rw [hcarrier]
      exact ⟨u, rfl⟩
    have hs_le_u : sourceBoundaryParam e ≤ u := by
      by_contra hnot
      have hu_lt_s : u < sourceBoundaryParam e := lt_of_not_ge hnot
      have hp_closed := source_prefix_closed_vertexDisk e u (le_of_lt hu_lt_s)
      have hp_not_ball :
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) :=
        havoids_vertices (edgeEndpoints.edgeSourceVertex e)
      have hp_sphere :
          edgeParam e u ∈
            Metric.sphere
              (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) := by
        have hclosed_dist :
            dist (edgeParam e u)
                (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e)) ≤
              controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e) := by
          simpa [Metric.mem_closedBall] using hp_closed
        have hnot_lt :
            ¬ dist (edgeParam e u)
                (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e)) <
              controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e) := by
          intro hlt
          exact hp_not_ball (by simpa [Metric.mem_ball] using hlt)
        have hdist :
            dist (edgeParam e u)
                (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e)) =
              controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e) :=
          le_antisymm hclosed_dist (le_of_not_gt hnot_lt)
        rw [Metric.mem_sphere, dist_eq_norm]
        simpa only [dist_eq_norm] using hdist
      have hp_eq_source :
          edgeParam e u = edgeEndpoints.sourceBoundaryPoint e :=
        edgeEndpoints.sourceBoundary_unique e (edgeParam e u)
          hp_sphere hp_on_carrier
      have hu_eq_s : u = sourceBoundaryParam e := by
        apply hinj
        exact hp_eq_source.trans (sourceBoundaryParam_eq e).symm
      rw [hu_eq_s] at hu_lt_s
      exact (lt_irrefl (sourceBoundaryParam e)) hu_lt_s
    have hu_le_t : u ≤ targetBoundaryParam e := by
      by_contra hnot
      have ht_lt_u : targetBoundaryParam e < u := lt_of_not_ge hnot
      have hp_closed := target_suffix_closed_vertexDisk e u (le_of_lt ht_lt_u)
      have hp_not_ball :
          edgeParam e u ∉
            Metric.ball
              (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) :=
        havoids_vertices (edgeEndpoints.edgeTargetVertex e)
      have hp_sphere :
          edgeParam e u ∈
            Metric.sphere
              (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
              (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) := by
        have hclosed_dist :
            dist (edgeParam e u)
                (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e)) ≤
              controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e) := by
          simpa [Metric.mem_closedBall] using hp_closed
        have hnot_lt :
            ¬ dist (edgeParam e u)
                (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e)) <
              controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e) := by
          intro hlt
          exact hp_not_ball (by simpa [Metric.mem_ball] using hlt)
        have hdist :
            dist (edgeParam e u)
                (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e)) =
              controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e) :=
          le_antisymm hclosed_dist (le_of_not_gt hnot_lt)
        rw [Metric.mem_sphere, dist_eq_norm]
        simpa only [dist_eq_norm] using hdist
      have hp_eq_target :
          edgeParam e u = edgeEndpoints.targetBoundaryPoint e :=
        edgeEndpoints.targetBoundary_unique e (edgeParam e u)
          hp_sphere hp_on_carrier
      have hu_eq_t : u = targetBoundaryParam e := by
        apply hinj
        exact hp_eq_target.trans (targetBoundaryParam_eq e).symm
      rw [hu_eq_t] at ht_lt_u
      exact (lt_irrefl (targetBoundaryParam e)) ht_lt_u
    rcases
      retained_interval_skeleton_intersection_disk_image_coverage
        e u hs_le_u hu_le_t havoids_intersections with
      ⟨i, howner, himage⟩
    refine ⟨i, howner, ?_⟩
    change edgeParam e u ∈ edgeParam (S.owner i) ''
      Set.Icc (S.sourceParam i) (S.targetParam i)
    exact himage
