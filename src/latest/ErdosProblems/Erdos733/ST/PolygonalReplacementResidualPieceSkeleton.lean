import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualPieceSkeletonData
import ErdosProblems.Erdos733.ST.GeometricArcDrawing
import ErdosProblems.Erdos733.ST.PolygonalReplacementRetainedParameterIntervals


open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementResidualPieceSkeleton]
lemma PolygonalReplacementResidualPieceSkeleton {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (sourceBoundaryParam targetBoundaryParam : G.edgeFinset → Set.Icc (0 : ℝ) 1)
    (intersectionCenterParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (intersectionLeftParam intersectionRightParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (retained_parameter_intervals :
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
                        intersectionRightParam (cuts[n].2))) :
    Nonempty
      (PolygonalReplacementResidualPieceSkeletonData G D sourceBoundaryParam
        targetBoundaryParam intersectionCenterParam intersectionLeftParam
        intersectionRightParam) := by
-- BODY
  classical
  let cuts :
      (e : G.edgeFinset) →
        List {x : {p // p ∈ D.intersectionPoints} //
          x.1 ∈ D.edgeRelativeInterior e} := fun e =>
    Classical.choose (retained_parameter_intervals e)
  let intervals :
      G.edgeFinset → List (Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) := fun e =>
    Classical.choose ((Classical.choose_spec (retained_parameter_intervals e)).2)
  have cut_spec :
      ∀ e,
        (cuts e).Nodup ∧
          (∀ x : {x : {p // p ∈ D.intersectionPoints} //
              x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts e) ∧
          (∀ i j (hi : i < (cuts e).length) (hj : j < (cuts e).length),
            i < j →
              intersectionCenterParam ((cuts e)[i].2) <
                intersectionCenterParam ((cuts e)[j].2)) ∧
          (∀ x : {x : {p // p ∈ D.intersectionPoints} //
              x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts e →
            sourceBoundaryParam e < intersectionLeftParam x.2) ∧
          (∀ x : {x : {p // p ∈ D.intersectionPoints} //
              x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts e →
            intersectionLeftParam x.2 < intersectionCenterParam x.2 ∧
              intersectionCenterParam x.2 < intersectionRightParam x.2) ∧
          (∀ x : {x : {p // p ∈ D.intersectionPoints} //
              x.1 ∈ D.edgeRelativeInterior e}, x ∈ cuts e →
            intersectionRightParam x.2 < targetBoundaryParam e) ∧
          (∀ n (hn : n + 1 < (cuts e).length),
            intersectionRightParam ((cuts e)[n].2) <
              intersectionLeftParam ((cuts e)[n + 1].2)) ∧
          (∀ i j (hi : i < (cuts e).length) (hj : j < (cuts e).length),
            i < j →
              intersectionRightParam ((cuts e)[i].2) <
                intersectionLeftParam ((cuts e)[j].2)) := by
    intro e
    exact (Classical.choose_spec (retained_parameter_intervals e)).1
  have intervals_spec :
      ∀ e,
        (intervals e).length = (cuts e).length + 1 ∧
          (∀ (n : ℕ) (a b : Set.Icc (0 : ℝ) 1),
            (intervals e)[n]? = some (a, b) → a < b) ∧
          (intervals e).head?.map Prod.fst = some (sourceBoundaryParam e) ∧
          (intervals e).getLast?.map Prod.snd = some (targetBoundaryParam e) ∧
          (∀ (n : ℕ) (hn : n < (cuts e).length),
            (intervals e)[n]?.map Prod.snd =
                some (intersectionLeftParam ((cuts e)[n].2)) ∧
              (intervals e)[n + 1]?.map Prod.fst =
                  some (intersectionRightParam ((cuts e)[n].2)) ∧
                intersectionLeftParam ((cuts e)[n].2) <
                    intersectionCenterParam ((cuts e)[n].2) ∧
                  intersectionCenterParam ((cuts e)[n].2) <
                    intersectionRightParam ((cuts e)[n].2)) := by
    intro e
    exact Classical.choose_spec
      ((Classical.choose_spec (retained_parameter_intervals e)).2)
  let PieceIndex : Type u :=
    Sigma (fun e : G.edgeFinset => Fin ((intervals e).length))
  let owner : PieceIndex → G.edgeFinset := fun i => i.1
  let sourceParam : PieceIndex → Set.Icc (0 : ℝ) 1 := fun i =>
    ((intervals i.1)[i.2]).1
  let targetParam : PieceIndex → Set.Icc (0 : ℝ) 1 := fun i =>
    ((intervals i.1)[i.2]).2
  let edgePieceOrder : G.edgeFinset → List PieceIndex := fun e =>
    List.ofFn (fun n : Fin ((intervals e).length) => (⟨e, n⟩ : PieceIndex))
  refine ⟨
    { retainedIntervals := intervals
      cutList := cuts
      cutList_nodup := ?_
      cutList_mem_all := ?_
      cutList_center_strict := ?_
      cutList_source_lt_left := ?_
      cutList_left_center_right := ?_
      cutList_right_lt_target := ?_
      cutList_consecutive_separation := ?_
      cutList_interval_order := ?_
      retainedIntervals_length_eq_cutList_length := ?_
      retainedIntervals_head_source := ?_
      retainedIntervals_last_target := ?_
      retainedIntervals_cut_gap := ?_
      pieceIndex := PieceIndex
      pieceIndex_fintype := by
        dsimp [PieceIndex]
        infer_instance
      owner := owner
      sourceParam := sourceParam
      targetParam := targetParam
      edgePieceOrder := edgePieceOrder
      edgePieceOrder_nonempty := ?_
      edgePieceOrder_nodup := ?_
      edgePieceOrder_owner_iff := ?_
      edgePieceOrder_length_eq_retainedIntervals_length := ?_
      edgePieceOrder_matches_retainedIntervals := ?_
      sourceParam_lt_targetParam := ?_
      edgePieceOrder_first_sourceParam := ?_
      edgePieceOrder_last_targetParam := ?_
      edgePieceOrder_consecutive_param_order := ?_ }⟩
  · intro e
    exact (cut_spec e).1
  · intro e x
    exact (cut_spec e).2.1 x
  · intro e i j hi hj hij
    exact (cut_spec e).2.2.1 i j hi hj hij
  · intro e x hx
    exact (cut_spec e).2.2.2.1 x hx
  · intro e x hx
    exact (cut_spec e).2.2.2.2.1 x hx
  · intro e x hx
    exact (cut_spec e).2.2.2.2.2.1 x hx
  · intro e n hn
    exact (cut_spec e).2.2.2.2.2.2.1 n hn
  · intro e i j hi hj hij
    exact (cut_spec e).2.2.2.2.2.2.2 i j hi hj hij
  · intro e
    exact (intervals_spec e).1
  · intro e
    exact (intervals_spec e).2.2.1
  · intro e
    exact (intervals_spec e).2.2.2.1
  · intro e n hn
    exact (intervals_spec e).2.2.2.2 n hn
  · intro e
    have hlen : (intervals e).length = (cuts e).length + 1 :=
      (intervals_spec e).1
    simp [edgePieceOrder, hlen]
  · intro e
    rw [List.nodup_ofFn]
    intro a b hab
    simpa [PieceIndex] using hab
  · intro e i
    constructor
    · intro hi
      rw [List.mem_ofFn] at hi
      rcases hi with ⟨n, hn⟩
      simpa [owner] using congrArg Sigma.fst hn.symm
    · intro hi
      subst hi
      rcases i with ⟨e, n⟩
      rw [List.mem_ofFn]
      exact ⟨n, rfl⟩
  · intro e
    simp [edgePieceOrder]
  · intro e n hn
    have hlen_order : (edgePieceOrder e).length = (intervals e).length := by
      simp [edgePieceOrder]
    have hn_intervals : n < (intervals e).length := by
      simpa [hlen_order] using hn
    have hget_order :
        (edgePieceOrder e)[n] =
          (⟨e, ⟨n, hn_intervals⟩⟩ : PieceIndex) := by
      simp [edgePieceOrder]
    have hget_interval :
        (intervals e)[n]? = some ((intervals e)[n]'hn_intervals) := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨hn_intervals, rfl⟩
    simp [hget_order, sourceParam, targetParam, hget_interval]
  · intro i
    rcases i with ⟨e, n⟩
    let interval := (intervals e)[n]
    have hsome : (intervals e)[n.1]? = some interval := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨n.2, rfl⟩
    simpa [sourceParam, targetParam, interval] using
      (intervals_spec e).2.1 n.1 interval.1 interval.2 hsome
  · intro e i hhead
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_some_iff] at hhead
    rcases hhead with ⟨hpos_order, hi⟩
    have hpos_intervals : 0 < (intervals e).length := by
      simpa [edgePieceOrder] using hpos_order
    have horder_get :
        (edgePieceOrder e)[0] =
          (⟨e, ⟨0, hpos_intervals⟩⟩ : PieceIndex) := by
      simp [edgePieceOrder]
    have hi_eq : i = (⟨e, ⟨0, hpos_intervals⟩⟩ : PieceIndex) := by
      exact hi.symm.trans horder_get
    have hinterval_get : (intervals e)[0]? =
        some ((intervals e)[0]'hpos_intervals) := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨hpos_intervals, rfl⟩
    have hfst : ((intervals e)[0]'hpos_intervals).1 =
        sourceBoundaryParam e := by
      have hhead_interval := (intervals_spec e).2.2.1
      rw [List.head?_eq_getElem?, hinterval_get] at hhead_interval
      simpa using hhead_interval
    simpa [sourceParam, hi_eq] using hfst
  · intro e i hlast
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getElem?_eq_some_iff] at hlast
    rcases hlast with ⟨hlast_order, hi⟩
    have hlast_intervals :
        (edgePieceOrder e).length - 1 < (intervals e).length := by
      simpa [edgePieceOrder] using hlast_order
    have horder_get :
        (edgePieceOrder e)[(edgePieceOrder e).length - 1] =
          (⟨e, ⟨(edgePieceOrder e).length - 1, hlast_intervals⟩⟩ :
            PieceIndex) := by
      simp [edgePieceOrder]
    have hi_eq :
        i = (⟨e, ⟨(edgePieceOrder e).length - 1, hlast_intervals⟩⟩ :
          PieceIndex) := by
      exact hi.symm.trans horder_get
    have hlength_order : (edgePieceOrder e).length = (intervals e).length := by
      simp [edgePieceOrder]
    have hlast_intervals' :
        (intervals e).length - 1 < (intervals e).length := by
      rwa [hlength_order] at hlast_intervals
    have hindex_eq :
        (edgePieceOrder e).length - 1 = (intervals e).length - 1 := by
      rw [hlength_order]
    have hinterval_get : (intervals e)[(intervals e).length - 1]? =
        some ((intervals e)[(intervals e).length - 1]'hlast_intervals') := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨hlast_intervals', rfl⟩
    have hsnd : ((intervals e)[(intervals e).length - 1]'hlast_intervals').2 =
        targetBoundaryParam e := by
      have hlast_interval := (intervals_spec e).2.2.2.1
      rw [List.getLast?_eq_getElem?, hinterval_get] at hlast_interval
      simpa using hlast_interval
    rw [hi_eq]
    simpa [targetParam, hindex_eq] using hsnd
  · intro e n hn
    have hlen_order : (edgePieceOrder e).length = (intervals e).length := by
      simp [edgePieceOrder]
    have hn_intervals : n + 1 < (intervals e).length := by
      simpa [hlen_order] using hn
    have hn_left : n < (intervals e).length := by omega
    have hn_right : n + 1 < (intervals e).length := hn_intervals
    have hget_left :
        (edgePieceOrder e)[n] =
          (⟨e, ⟨n, hn_left⟩⟩ : PieceIndex) := by
      simp [edgePieceOrder]
    have hget_right :
        (edgePieceOrder e)[n + 1] =
          (⟨e, ⟨n + 1, hn_right⟩⟩ : PieceIndex) := by
      simp [edgePieceOrder]
    have hn_cuts : n < (cuts e).length := by
      have hlen := (intervals_spec e).1
      omega
    rcases (intervals_spec e).2.2.2.2 n hn_cuts with
      ⟨hend_left, hstart_right, hleft_center, hcenter_right⟩
    have hleft_get : (intervals e)[n]? =
        some ((intervals e)[n]'hn_left) := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨hn_left, rfl⟩
    have hright_get : (intervals e)[n + 1]? =
        some ((intervals e)[n + 1]'hn_right) := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨hn_right, rfl⟩
    have htarget_eq :
        ((intervals e)[n]'hn_left).2 =
          intersectionLeftParam ((cuts e)[n].2) := by
      rw [hleft_get] at hend_left
      simpa using hend_left
    have hsource_eq :
        ((intervals e)[n + 1]'hn_right).1 =
          intersectionRightParam ((cuts e)[n].2) := by
      rw [hright_get] at hstart_right
      simpa using hstart_right
    have hgap :
        ((intervals e)[n]'hn_left).2 <
          ((intervals e)[n + 1]'hn_right).1 := by
      rw [htarget_eq, hsource_eq]
      exact lt_trans hleft_center hcenter_right
    simpa [targetParam, sourceParam, hget_left, hget_right] using hgap
