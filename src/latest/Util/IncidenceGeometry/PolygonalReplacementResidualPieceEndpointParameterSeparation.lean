import Util.IncidenceGeometry.PolygonalReplacementResidualPieceData
import Util.IncidenceGeometry.PositiveSeparation

open Classical
noncomputable section

universe u

lemma PolygonalReplacementResidualPieceEndpointParameterSeparation {V : Type u}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (residualPieceData :
      PolygonalReplacementResidualPieceData G D controlDisks boundaryPoints
        edgeEndpoints)
    (i : residualPieceData.pieceIndex) :
    ∃ m : Set.Icc (0 : ℝ) 1,
      residualPieceData.sourceParam i < m ∧
        m < residualPieceData.targetParam i ∧
          ∃ εs : ℝ, 0 < εs ∧
            (∀ u : Set.Icc (0 : ℝ) 1,
              u ≤ residualPieceData.targetParam i →
                residualPieceData.edgeParam (residualPieceData.owner i) u ∈
                  Metric.ball (residualPieceData.source i) εs →
                  u < m) ∧
            ∃ εt : ℝ, 0 < εt ∧
              (∀ u : Set.Icc (0 : ℝ) 1,
                residualPieceData.sourceParam i ≤ u →
                  residualPieceData.edgeParam (residualPieceData.owner i) u ∈
                    Metric.ball (residualPieceData.target i) εt →
                    m < u) := by
  classical
  let e : G.edgeFinset := residualPieceData.owner i
  let sParam : Set.Icc (0 : ℝ) 1 := residualPieceData.sourceParam i
  let tParam : Set.Icc (0 : ℝ) 1 := residualPieceData.targetParam i
  rcases residualPieceData.edgeParam_spec e with
    ⟨hedge_cont, hedge_inj, _hsource, _htarget, _hcarrier, _hrel⟩
  have hs_lt_t : sParam < tParam := by
    simpa [sParam, tParam] using residualPieceData.sourceParam_lt_targetParam i
  have hs_val_lt_t_val : sParam.1 < tParam.1 := hs_lt_t
  let m : Set.Icc (0 : ℝ) 1 :=
    ⟨(sParam.1 + tParam.1) / 2, by
      constructor
      · have hs_nonneg : (0 : ℝ) ≤ sParam.1 := sParam.2.1
        have ht_nonneg : (0 : ℝ) ≤ tParam.1 := tParam.2.1
        linarith
      · have hs_le_one : sParam.1 ≤ (1 : ℝ) := sParam.2.2
        have ht_le_one : tParam.1 ≤ (1 : ℝ) := tParam.2.2
        linarith⟩
  have hs_lt_m : sParam < m := by
    change sParam.1 < (sParam.1 + tParam.1) / 2
    linarith
  have hm_lt_t : m < tParam := by
    change (sParam.1 + tParam.1) / 2 < tParam.1
    linarith
  let rightImage : Set (EuclideanSpace ℝ (Fin 2)) :=
    residualPieceData.edgeParam e '' Set.Icc m tParam
  have hright_nonempty : rightImage.Nonempty := by
    refine ⟨residualPieceData.edgeParam e tParam, ?_⟩
    exact ⟨tParam, ⟨hm_lt_t.le, le_rfl⟩, rfl⟩
  have hright_compact : IsCompact rightImage := by
    dsimp [rightImage]
    exact isCompact_Icc.image hedge_cont
  have hsource_right_disjoint :
      Disjoint ({residualPieceData.source i} : Set (EuclideanSpace ℝ (Fin 2)))
        rightImage := by
    rw [Set.disjoint_left]
    intro p hp_source hp_right
    rw [Set.mem_singleton_iff] at hp_source
    rcases hp_right with ⟨u, hu_interval, hpu⟩
    have hedge_eq :
        residualPieceData.edgeParam e sParam =
          residualPieceData.edgeParam e u := by
      calc
        residualPieceData.edgeParam e sParam = residualPieceData.source i := by
          exact (by simpa [e, sParam] using
            (residualPieceData.source_eq_edgeParam i).symm)
        _ = p := hp_source.symm
        _ = residualPieceData.edgeParam e u := hpu.symm
    have hsu : sParam = u := hedge_inj hedge_eq
    have hm_le_s : m ≤ sParam := by
      simpa [hsu] using hu_interval.1
    exact (not_lt_of_ge hm_le_s) hs_lt_m
  obtain ⟨εs, hεs_pos, hεs_sep⟩ :=
    PositiveSeparation
      (A := ({residualPieceData.source i} :
        Set (EuclideanSpace ℝ (Fin 2))))
      (B := rightImage)
      ⟨residualPieceData.source i, by simp⟩ hright_nonempty
      isCompact_singleton hright_compact hsource_right_disjoint
  have source_ball_left :
      ∀ u : Set.Icc (0 : ℝ) 1,
        u ≤ residualPieceData.targetParam i →
          residualPieceData.edgeParam (residualPieceData.owner i) u ∈
            Metric.ball (residualPieceData.source i) εs →
            u < m := by
    intro u hu_target hu_ball
    by_contra hnot
    have hm_le_u : m ≤ u := le_of_not_gt hnot
    have hu_right : residualPieceData.edgeParam e u ∈ rightImage := by
      exact ⟨u, ⟨hm_le_u, by simpa [tParam] using hu_target⟩, rfl⟩
    have hsep := hεs_sep (residualPieceData.source i) (by simp)
      (residualPieceData.edgeParam e u) hu_right
    have hdist_lt :
        dist (residualPieceData.source i) (residualPieceData.edgeParam e u) <
          εs := by
      rw [Metric.mem_ball] at hu_ball
      simpa [e, dist_comm] using hu_ball
    exact (not_lt_of_ge hsep) hdist_lt
  let leftImage : Set (EuclideanSpace ℝ (Fin 2)) :=
    residualPieceData.edgeParam e '' Set.Icc sParam m
  have hleft_nonempty : leftImage.Nonempty := by
    refine ⟨residualPieceData.edgeParam e sParam, ?_⟩
    exact ⟨sParam, ⟨le_rfl, hs_lt_m.le⟩, rfl⟩
  have hleft_compact : IsCompact leftImage := by
    dsimp [leftImage]
    exact isCompact_Icc.image hedge_cont
  have htarget_left_disjoint :
      Disjoint ({residualPieceData.target i} : Set (EuclideanSpace ℝ (Fin 2)))
        leftImage := by
    rw [Set.disjoint_left]
    intro p hp_target hp_left
    rw [Set.mem_singleton_iff] at hp_target
    rcases hp_left with ⟨u, hu_interval, hpu⟩
    have hedge_eq :
        residualPieceData.edgeParam e tParam =
          residualPieceData.edgeParam e u := by
      calc
        residualPieceData.edgeParam e tParam = residualPieceData.target i := by
          exact (by simpa [e, tParam] using
            (residualPieceData.target_eq_edgeParam i).symm)
        _ = p := hp_target.symm
        _ = residualPieceData.edgeParam e u := hpu.symm
    have htu : tParam = u := hedge_inj hedge_eq
    have ht_le_m : tParam ≤ m := by
      simpa [htu] using hu_interval.2
    exact (not_lt_of_ge ht_le_m) hm_lt_t
  obtain ⟨εt, hεt_pos, hεt_sep⟩ :=
    PositiveSeparation
      (A := ({residualPieceData.target i} :
        Set (EuclideanSpace ℝ (Fin 2))))
      (B := leftImage)
      ⟨residualPieceData.target i, by simp⟩ hleft_nonempty
      isCompact_singleton hleft_compact htarget_left_disjoint
  have target_ball_right :
      ∀ u : Set.Icc (0 : ℝ) 1,
        residualPieceData.sourceParam i ≤ u →
          residualPieceData.edgeParam (residualPieceData.owner i) u ∈
            Metric.ball (residualPieceData.target i) εt →
            m < u := by
    intro u hu_source hu_ball
    by_contra hnot
    have hu_le_m : u ≤ m := le_of_not_gt hnot
    have hu_left : residualPieceData.edgeParam e u ∈ leftImage := by
      exact ⟨u, ⟨by simpa [sParam] using hu_source, hu_le_m⟩, rfl⟩
    have hsep := hεt_sep (residualPieceData.target i) (by simp)
      (residualPieceData.edgeParam e u) hu_left
    have hdist_lt :
        dist (residualPieceData.target i) (residualPieceData.edgeParam e u) <
          εt := by
      rw [Metric.mem_ball] at hu_ball
      simpa [e, dist_comm] using hu_ball
    exact (not_lt_of_ge hsep) hdist_lt
  exact ⟨m, hs_lt_m, hm_lt_t, εs, hεs_pos, source_ball_left,
    εt, hεt_pos, target_ball_right⟩
