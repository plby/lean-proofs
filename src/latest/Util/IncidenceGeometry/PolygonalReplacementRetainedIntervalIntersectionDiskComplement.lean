import Util.IncidenceGeometry.PolygonalReplacementControlDiskData
import Util.IncidenceGeometry.PolygonalReplacementIntersectionCutOpenBallIff
import Util.IncidenceGeometry.PolygonalReplacementResidualPieceSkeletonParameterBounds
import Util.IncidenceGeometry.PolygonalReplacementRetainedIntervalCutAvoidance
import Util.IncidenceGeometry.PolygonalReplacementRetainedIntervalCutCoverage

open Classical
noncomputable section

universe u

lemma PolygonalReplacementRetainedIntervalIntersectionDiskComplement {V : Type u}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
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
    (intersectionCenterParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
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
    (∀ i (u : Set.Icc (0 : ℝ) 1),
      S.sourceParam i ≤ u →
        u ≤ S.targetParam i →
          ∀ x : {q // q ∈ D.intersectionPoints},
            edgeParam (S.owner i) u ∉
              Metric.ball x.1 (controlDisks.intersectionRadius x)) ∧
      (∀ e (u : Set.Icc (0 : ℝ) 1),
        sourceBoundaryParam e ≤ u →
          u ≤ targetBoundaryParam e →
            (∀ x : {q // q ∈ D.intersectionPoints},
              edgeParam e u ∉
                Metric.ball x.1 (controlDisks.intersectionRadius x)) →
              ∃ i, S.owner i = e ∧ S.sourceParam i ≤ u ∧
                u ≤ S.targetParam i) ∧
        (∀ i (x : {q // q ∈ D.intersectionPoints}),
          Disjoint
            (edgeParam (S.owner i) ''
              Set.Icc (S.sourceParam i) (S.targetParam i))
            (Metric.ball x.1 (controlDisks.intersectionRadius x))) ∧
          (∀ e (u : Set.Icc (0 : ℝ) 1),
            sourceBoundaryParam e ≤ u →
              u ≤ targetBoundaryParam e →
                (∀ x : {q // q ∈ D.intersectionPoints},
                  edgeParam e u ∉
                    Metric.ball x.1 (controlDisks.intersectionRadius x)) →
                  ∃ i, S.owner i = e ∧
                    edgeParam e u ∈
                      edgeParam (S.owner i) ''
                        Set.Icc (S.sourceParam i) (S.targetParam i)) := by
  classical
  have parameter_bounds :=
    PolygonalReplacementResidualPieceSkeletonParameterBounds G
      sourceBoundaryParam targetBoundaryParam S
  have avoids_intersection_disks :
      ∀ i (u : Set.Icc (0 : ℝ) 1),
        S.sourceParam i ≤ u →
          u ≤ S.targetParam i →
            ∀ x : {q // q ∈ D.intersectionPoints},
              edgeParam (S.owner i) u ∉
                Metric.ball x.1 (controlDisks.intersectionRadius x) := by
    intro i u hsource_le_u hu_le_target x hball
    let e : G.edgeFinset := S.owner i
    have hp_closed :
        edgeParam e u ∈ Metric.closedBall x.1
            (controlDisks.intersectionRadius x) :=
      Metric.ball_subset_closedBall hball
    have hp_carrier : edgeParam e u ∈ D.edgeCarrier e := by
      rcases edgeParam_spec e with
        ⟨_hcont, _hinj, _hsource, _htarget, hcarrier, _hrel⟩
      rw [hcarrier]
      exact ⟨u, rfl⟩
    have hx_rel : x.1 ∈ D.edgeRelativeInterior e :=
      controlDisks.intersection_disk_meets_only_passing_edges hp_closed hp_carrier
    have hmiddle_source : sourceBoundaryParam e ≤ u := by
      exact le_trans (parameter_bounds.1 i) hsource_le_u
    have hmiddle_target : u ≤ targetBoundaryParam e := by
      exact le_trans hu_le_target (parameter_bounds.2 i)
    have hinside_cut :
        intersectionLeftParam hx_rel < u ∧
          u < intersectionRightParam hx_rel := by
      exact
        (intersection_open_ball_iff_cut_interval (x := x) (e := e)
          hx_rel u hmiddle_source hmiddle_target).mp hball
    have hi_mem : i ∈ S.edgePieceOrder e :=
      (S.edgePieceOrder_owner_iff e i).2 rfl
    rcases List.getElem_of_mem hi_mem with
      ⟨n, hn, hget_piece⟩
    have hinterval_some :
        (S.retainedIntervals e)[n]? =
          some (S.sourceParam i, S.targetParam i) := by
      have hmatch :=
        S.edgePieceOrder_matches_retainedIntervals e n hn
      simpa [hget_piece] using hmatch
    have hcut_mem :
        (⟨x, hx_rel⟩ : {x : {p // p ∈ D.intersectionPoints} //
            x.1 ∈ D.edgeRelativeInterior e}) ∈ S.cutList e :=
      S.cutList_mem_all e ⟨x, hx_rel⟩
    rcases List.getElem_of_mem hcut_mem with
      ⟨k, hk, hget_cut⟩
    have hnot_cut :=
      PolygonalReplacementRetainedIntervalCutAvoidance
        (S.cutList e)
        (fun y => intersectionLeftParam y.2)
        (fun y => intersectionCenterParam y.2)
        (fun y => intersectionRightParam y.2)
        (S.retainedIntervals e)
        (S.retainedIntervals_length_eq_cutList_length e)
        (S.retainedIntervals_cut_gap e)
        (S.cutList_interval_order e)
        n (S.sourceParam i) (S.targetParam i) hinterval_some
        k hk u hsource_le_u hu_le_target
    exact hnot_cut (by simpa [hget_cut] using hinside_cut)
  have intersection_disk_coverage :
      ∀ e (u : Set.Icc (0 : ℝ) 1),
        sourceBoundaryParam e ≤ u →
          u ≤ targetBoundaryParam e →
            (∀ x : {q // q ∈ D.intersectionPoints},
              edgeParam e u ∉
                Metric.ball x.1 (controlDisks.intersectionRadius x)) →
              ∃ i, S.owner i = e ∧ S.sourceParam i ≤ u ∧
                u ≤ S.targetParam i := by
    intro e u hsource_le hu_le_target havoids_intersections
    have havoid_cuts :
        ∀ k (hk : k < (S.cutList e).length),
          ¬ (intersectionLeftParam ((S.cutList e)[k].2) < u ∧
            u < intersectionRightParam ((S.cutList e)[k].2)) := by
      intro k hk hinside
      have hball :
          edgeParam e u ∈
            Metric.ball ((S.cutList e)[k].1).1
              (controlDisks.intersectionRadius ((S.cutList e)[k].1)) := by
        exact
          (intersection_open_ball_iff_cut_interval
            (x := (S.cutList e)[k].1) (e := e)
            ((S.cutList e)[k].2) u hsource_le hu_le_target).mpr hinside
      exact havoids_intersections ((S.cutList e)[k].1) hball
    rcases
      PolygonalReplacementRetainedIntervalCutCoverage
        (sourceBoundaryParam e) (targetBoundaryParam e)
        (S.cutList e)
        (fun y => intersectionLeftParam y.2)
        (fun y => intersectionRightParam y.2)
        (S.retainedIntervals e)
        (S.retainedIntervals_length_eq_cutList_length e)
        (S.retainedIntervals_head_source e)
        (S.retainedIntervals_last_target e)
        (fun n hn =>
          ⟨(S.retainedIntervals_cut_gap e n hn).1,
            (S.retainedIntervals_cut_gap e n hn).2.1⟩)
        u hsource_le hu_le_target havoid_cuts with
      ⟨n, a, b, hsome, ha_le_u, hu_le_b⟩
    have hn_intervals : n < (S.retainedIntervals e).length := by
      exact (List.getElem?_eq_some_iff.mp hsome).1
    have hn_order : n < (S.edgePieceOrder e).length := by
      rw [S.edgePieceOrder_length_eq_retainedIntervals_length e]
      exact hn_intervals
    let i : S.pieceIndex := (S.edgePieceOrder e)[n]
    have hi_mem : i ∈ S.edgePieceOrder e := by
      exact List.getElem_mem hn_order
    have howner : S.owner i = e :=
      (S.edgePieceOrder_owner_iff e i).1 hi_mem
    have hmatch :
        (S.retainedIntervals e)[n]? =
          some (S.sourceParam i, S.targetParam i) := by
      simpa [i] using
        S.edgePieceOrder_matches_retainedIntervals e n hn_order
    have hpairs :
        (a, b) = (S.sourceParam i, S.targetParam i) :=
      Option.some.inj (hsome.symm.trans hmatch)
    have hsource_eq : a = S.sourceParam i :=
      congrArg Prod.fst hpairs
    have htarget_eq : b = S.targetParam i :=
      congrArg Prod.snd hpairs
    refine ⟨i, howner, ?_, ?_⟩
    · simpa [hsource_eq] using ha_le_u
    · simpa [htarget_eq] using hu_le_b
  have image_avoids_intersection_disks :
      ∀ i (x : {q // q ∈ D.intersectionPoints}),
        Disjoint
          (edgeParam (S.owner i) ''
            Set.Icc (S.sourceParam i) (S.targetParam i))
          (Metric.ball x.1 (controlDisks.intersectionRadius x)) := by
    intro i x
    rw [Set.disjoint_left]
    intro p hp hball
    rcases hp with ⟨u, hu, rfl⟩
    exact avoids_intersection_disks i u hu.1 hu.2 x hball
  have image_coverage :
      ∀ e (u : Set.Icc (0 : ℝ) 1),
        sourceBoundaryParam e ≤ u →
          u ≤ targetBoundaryParam e →
            (∀ x : {q // q ∈ D.intersectionPoints},
              edgeParam e u ∉
                Metric.ball x.1 (controlDisks.intersectionRadius x)) →
              ∃ i, S.owner i = e ∧
                edgeParam e u ∈
                  edgeParam (S.owner i) ''
                    Set.Icc (S.sourceParam i) (S.targetParam i) := by
    intro e u hsource_le hu_le_target havoids_intersections
    rcases intersection_disk_coverage e u hsource_le hu_le_target
        havoids_intersections with
      ⟨i, howner, hsource_piece, htarget_piece⟩
    refine ⟨i, howner, ?_⟩
    refine ⟨u, ⟨hsource_piece, htarget_piece⟩, ?_⟩
    simp [howner]
  exact ⟨avoids_intersection_disks, intersection_disk_coverage,
    image_avoids_intersection_disks, image_coverage⟩
