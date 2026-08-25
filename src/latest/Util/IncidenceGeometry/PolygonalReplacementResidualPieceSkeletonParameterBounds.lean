import Util.IncidenceGeometry.PolygonalReplacementResidualPieceSkeletonData

open Classical
noncomputable section

universe u

lemma PolygonalReplacementResidualPieceSkeletonParameterBounds {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] {D : GeometricArcDrawing G}
    (sourceBoundaryParam targetBoundaryParam :
      G.edgeFinset → Set.Icc (0 : ℝ) 1)
    {intersectionCenterParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1}
    {intersectionLeftParam intersectionRightParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1}
    (S : PolygonalReplacementResidualPieceSkeletonData G D
      sourceBoundaryParam targetBoundaryParam intersectionCenterParam
      intersectionLeftParam intersectionRightParam) :
    (∀ i, sourceBoundaryParam (S.owner i) ≤ S.sourceParam i) ∧
      (∀ i, S.targetParam i ≤ targetBoundaryParam (S.owner i)) := by
  classical
  have exists_get_of_mem :
      ∀ {α : Type u} (l : List α) (a : α), a ∈ l →
        ∃ n, ∃ hn : n < l.length, l[n] = a := by
    intro α l a ha
    induction l with
    | nil => simp at ha
    | cons b bs ih =>
        simp at ha
        rcases ha with rfl | ha
        · exact ⟨0, by simp, by simp⟩
        · rcases ih ha with ⟨n, hn, hget⟩
          exact ⟨n + 1, by simpa using Nat.succ_lt_succ hn,
            by simpa using hget⟩
  constructor
  · intro i
    let e := S.owner i
    have hi_mem : i ∈ S.edgePieceOrder e :=
      (S.edgePieceOrder_owner_iff e i).2 rfl
    have locate :
        ∃ n, ∃ hn : n < (S.edgePieceOrder e).length,
          (S.edgePieceOrder e)[n] = i :=
      exists_get_of_mem (S.edgePieceOrder e) i hi_mem
    rcases locate with ⟨n, hn, hget⟩
    have source_le_get :
        ∀ m (hm : m < (S.edgePieceOrder e).length),
          sourceBoundaryParam e ≤ S.sourceParam ((S.edgePieceOrder e)[m]) := by
      intro m
      induction m with
      | zero =>
          intro hm
          have hhead :
              (S.edgePieceOrder e).head? = some ((S.edgePieceOrder e)[0]) := by
            rw [List.head?_eq_getElem?]
            rw [List.getElem?_eq_some_iff]
            exact ⟨hm, rfl⟩
          have hsrc :=
            S.edgePieceOrder_first_sourceParam e
              ((S.edgePieceOrder e)[0]) hhead
          exact le_of_eq hsrc.symm
      | succ m ih =>
          intro hm
          have hm_prev : m < (S.edgePieceOrder e).length := by omega
          have hprev := ih hm_prev
          have hprev_lt_target :
              S.sourceParam ((S.edgePieceOrder e)[m]) <
                S.targetParam ((S.edgePieceOrder e)[m]) :=
            S.sourceParam_lt_targetParam ((S.edgePieceOrder e)[m])
          have hgap :
              S.targetParam ((S.edgePieceOrder e)[m]) <
                S.sourceParam ((S.edgePieceOrder e)[m + 1]) :=
            S.edgePieceOrder_consecutive_param_order e m (by simpa using hm)
          exact le_trans (le_trans hprev hprev_lt_target.le) hgap.le
    have := source_le_get n hn
    simpa [hget, e] using this
  · intro i
    let e := S.owner i
    have hi_mem : i ∈ S.edgePieceOrder e :=
      (S.edgePieceOrder_owner_iff e i).2 rfl
    have locate :
        ∃ n, ∃ hn : n < (S.edgePieceOrder e).length,
          (S.edgePieceOrder e)[n] = i :=
      exists_get_of_mem (S.edgePieceOrder e) i hi_mem
    rcases locate with ⟨n, hn, hget⟩
    have hlen_pos : 0 < (S.edgePieceOrder e).length :=
      Nat.pos_of_ne_zero (S.edgePieceOrder_nonempty e)
    let last : ℕ := (S.edgePieceOrder e).length - 1
    have hlast_lt : last < (S.edgePieceOrder e).length := by
      dsimp [last]
      omega
    have hn_le_last : n ≤ last := by
      dsimp [last]
      omega
    have target_le_m :
        ∀ m (hm : m < (S.edgePieceOrder e).length), n ≤ m →
          S.targetParam ((S.edgePieceOrder e)[n]'hn) ≤
            S.targetParam ((S.edgePieceOrder e)[m]'hm) := by
      intro m hm hnm
      induction m, hnm using Nat.le_induction with
      | base =>
          simp
      | succ m hnm ih =>
          have hm_len : m + 1 < (S.edgePieceOrder e).length := hm
          have hm_prev : m < (S.edgePieceOrder e).length := by omega
          have ih' :
              S.targetParam ((S.edgePieceOrder e)[n]'hn) ≤
                S.targetParam ((S.edgePieceOrder e)[m]'hm_prev) :=
            ih hm_prev
          have hgap :
              S.targetParam ((S.edgePieceOrder e)[m]'hm_prev) <
                S.sourceParam ((S.edgePieceOrder e)[m + 1]'hm_len) := by
            simpa using
              S.edgePieceOrder_consecutive_param_order e m (by simpa using hm_len)
          have hsrc_lt_tgt :
              S.sourceParam ((S.edgePieceOrder e)[m + 1]'hm_len) <
                S.targetParam ((S.edgePieceOrder e)[m + 1]'hm_len) :=
            S.sourceParam_lt_targetParam ((S.edgePieceOrder e)[m + 1]'hm_len)
          exact le_trans ih' (le_of_lt (lt_trans hgap hsrc_lt_tgt))
    have hlast_some :
        (S.edgePieceOrder e).getLast? =
          some ((S.edgePieceOrder e)[last]'hlast_lt) := by
      rw [List.getLast?_eq_getElem?]
      rw [List.getElem?_eq_some_iff]
      refine ⟨?_, rfl⟩
      omega
    have hlast_eq :=
      S.edgePieceOrder_last_targetParam e
        ((S.edgePieceOrder e)[last]'hlast_lt) hlast_some
    have htarget_to_last := target_le_m last hlast_lt hn_le_last
    have htarget_last :
        S.targetParam ((S.edgePieceOrder e)[last]'hlast_lt) =
          targetBoundaryParam e :=
      hlast_eq
    have : S.targetParam ((S.edgePieceOrder e)[n]) ≤ targetBoundaryParam e := by
      simpa [htarget_last] using htarget_to_last
    simpa [hget, e] using this
