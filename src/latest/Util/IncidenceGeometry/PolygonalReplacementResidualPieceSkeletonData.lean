import Util.IncidenceGeometry.GeometricArcDrawing

open Classical
noncomputable section

universe u

structure PolygonalReplacementResidualPieceSkeletonData {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (sourceBoundaryParam targetBoundaryParam : G.edgeFinset → Set.Icc (0 : ℝ) 1)
    (intersectionCenterParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (intersectionLeftParam intersectionRightParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1) where
  retainedIntervals : G.edgeFinset → List (Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1)
  cutList :
    (e : G.edgeFinset) →
      List {x : {p // p ∈ D.intersectionPoints} //
        x.1 ∈ D.edgeRelativeInterior e}
  cutList_nodup : ∀ e, (cutList e).Nodup
  cutList_mem_all :
    ∀ e (x : {x : {p // p ∈ D.intersectionPoints} //
        x.1 ∈ D.edgeRelativeInterior e}),
      x ∈ cutList e
  cutList_center_strict :
    ∀ e i j (hi : i < (cutList e).length) (hj : j < (cutList e).length),
      i < j →
        intersectionCenterParam ((cutList e)[i].2) <
          intersectionCenterParam ((cutList e)[j].2)
  cutList_source_lt_left :
    ∀ e (x : {x : {p // p ∈ D.intersectionPoints} //
        x.1 ∈ D.edgeRelativeInterior e}),
      x ∈ cutList e →
        sourceBoundaryParam e < intersectionLeftParam x.2
  cutList_left_center_right :
    ∀ e (x : {x : {p // p ∈ D.intersectionPoints} //
        x.1 ∈ D.edgeRelativeInterior e}),
      x ∈ cutList e →
        intersectionLeftParam x.2 < intersectionCenterParam x.2 ∧
          intersectionCenterParam x.2 < intersectionRightParam x.2
  cutList_right_lt_target :
    ∀ e (x : {x : {p // p ∈ D.intersectionPoints} //
        x.1 ∈ D.edgeRelativeInterior e}),
      x ∈ cutList e →
        intersectionRightParam x.2 < targetBoundaryParam e
  cutList_consecutive_separation :
    ∀ e n (hn : n + 1 < (cutList e).length),
      intersectionRightParam ((cutList e)[n].2) <
        intersectionLeftParam ((cutList e)[n + 1].2)
  cutList_interval_order :
    ∀ e i j (hi : i < (cutList e).length) (hj : j < (cutList e).length),
      i < j →
        intersectionRightParam ((cutList e)[i].2) <
          intersectionLeftParam ((cutList e)[j].2)
  retainedIntervals_length_eq_cutList_length :
    ∀ e, (retainedIntervals e).length = (cutList e).length + 1
  retainedIntervals_head_source :
    ∀ e, (retainedIntervals e).head?.map Prod.fst = some (sourceBoundaryParam e)
  retainedIntervals_last_target :
    ∀ e, (retainedIntervals e).getLast?.map Prod.snd = some (targetBoundaryParam e)
  retainedIntervals_cut_gap :
    ∀ e n (hn : n < (cutList e).length),
      (retainedIntervals e)[n]?.map Prod.snd =
          some (intersectionLeftParam ((cutList e)[n].2)) ∧
        (retainedIntervals e)[n + 1]?.map Prod.fst =
            some (intersectionRightParam ((cutList e)[n].2)) ∧
          intersectionLeftParam ((cutList e)[n].2) <
              intersectionCenterParam ((cutList e)[n].2) ∧
            intersectionCenterParam ((cutList e)[n].2) <
              intersectionRightParam ((cutList e)[n].2)
  pieceIndex : Type u
  pieceIndex_fintype : Fintype pieceIndex
  owner : pieceIndex → G.edgeFinset
  sourceParam : pieceIndex → Set.Icc (0 : ℝ) 1
  targetParam : pieceIndex → Set.Icc (0 : ℝ) 1
  edgePieceOrder : G.edgeFinset → List pieceIndex
  edgePieceOrder_nonempty : ∀ e, (edgePieceOrder e).length ≠ 0
  edgePieceOrder_nodup : ∀ e, (edgePieceOrder e).Nodup
  edgePieceOrder_owner_iff :
    ∀ e i, i ∈ edgePieceOrder e ↔ owner i = e
  edgePieceOrder_length_eq_retainedIntervals_length :
    ∀ e, (edgePieceOrder e).length = (retainedIntervals e).length
  edgePieceOrder_matches_retainedIntervals :
    ∀ e n (hn : n < (edgePieceOrder e).length),
      (retainedIntervals e)[n]? =
        some (sourceParam ((edgePieceOrder e)[n]),
          targetParam ((edgePieceOrder e)[n]))
  sourceParam_lt_targetParam : ∀ i, sourceParam i < targetParam i
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
