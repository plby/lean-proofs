import ErdosProblems.Erdos733.ST.PolygonalReplacementCircularResidualPieceCircleData

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementCircularTargetRetainedPoint]
lemma PolygonalReplacementCircularTargetRetainedPoint {V : Type u}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (residualPieceData :
      PolygonalReplacementResidualPieceData G D controlDisks boundaryPoints
        edgeEndpoints)
    (i : residualPieceData.pieceIndex)
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)}
    (hcircular :
      0 < r ∧
        Continuous γ ∧ Function.Injective γ ∧
        (∀ t, dist (γ t) c = r) ∧
        γ ⟨0, by simp⟩ = D.edgeSource (residualPieceData.owner i) ∧
        γ ⟨1, by simp⟩ = D.edgeTarget (residualPieceData.owner i) ∧
        D.edgeCarrier (residualPieceData.owner i) = Set.range γ ∧
        D.edgeRelativeInterior (residualPieceData.owner i) =
          Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
            γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ u : Set.Icc (0 : ℝ) 1,
        residualPieceData.sourceParam i ≤ u ∧
          u < residualPieceData.targetParam i ∧
            residualPieceData.edgeParam (residualPieceData.owner i) u ∈
              Metric.ball (residualPieceData.target i) ε ∧
            residualPieceData.edgeParam (residualPieceData.owner i) u ∈
              residualPieceData.originalPiece i ∧
            residualPieceData.edgeParam (residualPieceData.owner i) u ∈
              Metric.sphere c r ∧
            (∀ v : V,
              residualPieceData.edgeParam (residualPieceData.owner i) u ∉
                Metric.ball (D.vertexPlacement v)
                  (controlDisks.vertexRadius v)) ∧
            (∀ x : {p // p ∈ D.intersectionPoints},
              residualPieceData.edgeParam (residualPieceData.owner i) u ∉
                Metric.ball x.1 (controlDisks.intersectionRadius x)) := by
-- BODY
  classical
  intro ε hε
  let e : G.edgeFinset := residualPieceData.owner i
  let sourceParam : Set.Icc (0 : ℝ) 1 := residualPieceData.sourceParam i
  let targetParam : Set.Icc (0 : ℝ) 1 := residualPieceData.targetParam i
  let edgeParamAtOwner :
      Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) :=
    residualPieceData.edgeParam e
  rcases residualPieceData.edgeParam_spec e with
    ⟨hedgeParam_cont, _hedgeParam_inj, _hedgeParam_source,
      _hedgeParam_target, _hedgeParam_carrier, _hedgeParam_rel⟩
  rcases Metric.continuousAt_iff.mp hedgeParam_cont.continuousAt ε hε with
    ⟨δ, hδ_pos, hδ⟩
  have hsource_lt_target : sourceParam < targetParam := by
    simpa [sourceParam, targetParam] using
      residualPieceData.sourceParam_lt_targetParam i
  let η : ℝ := min ((targetParam.1 - sourceParam.1) / 2) (δ / 2)
  have htarget_sub_source_pos : 0 < targetParam.1 - sourceParam.1 :=
    sub_pos.mpr hsource_lt_target
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min (half_pos htarget_sub_source_pos) (half_pos hδ_pos)
  have hη_le_half_gap : η ≤ (targetParam.1 - sourceParam.1) / 2 :=
    min_le_left _ _
  have hη_le_half_delta : η ≤ δ / 2 := min_le_right _ _
  let u : Set.Icc (0 : ℝ) 1 :=
    ⟨targetParam.1 - η, by
      constructor
      · have hη_le_gap : η ≤ targetParam.1 - sourceParam.1 := by
          linarith
        have hsource_le_u : sourceParam.1 ≤ targetParam.1 - η := by
          linarith
        exact le_trans sourceParam.2.1 hsource_le_u
      · exact le_trans (sub_le_self targetParam.1 hη_pos.le) targetParam.2.2⟩
  have hsource_le_u : sourceParam ≤ u := by
    change sourceParam.1 ≤ targetParam.1 - η
    have hη_le_gap : η ≤ targetParam.1 - sourceParam.1 := by
      linarith
    linarith
  have hu_lt_target : u < targetParam := by
    change targetParam.1 - η < targetParam.1
    linarith
  have hu_dist_target : dist u targetParam < δ := by
    have hdist : dist u targetParam = η := by
      rw [Subtype.dist_eq, Real.dist_eq]
      change |(targetParam.1 - η) - targetParam.1| = η
      rw [show (targetParam.1 - η) - targetParam.1 = -η by ring,
        abs_neg, abs_of_pos hη_pos]
    rw [hdist]
    linarith
  have hu_ball :
      edgeParamAtOwner u ∈ Metric.ball (residualPieceData.target i) ε := by
    rw [Metric.mem_ball, residualPieceData.target_eq_edgeParam i]
    change dist (edgeParamAtOwner u) (edgeParamAtOwner targetParam) < ε
    exact hδ hu_dist_target
  have hu_interval :
      u ∈ Set.Icc (residualPieceData.sourceParam i)
        (residualPieceData.targetParam i) := by
    exact ⟨by simpa [sourceParam] using hsource_le_u,
      by simpa [targetParam] using hu_lt_target.le⟩
  have hu_original :
      residualPieceData.edgeParam (residualPieceData.owner i) u ∈
        residualPieceData.originalPiece i := by
    rw [residualPieceData.originalPiece_eq_parameter_interval i]
    exact ⟨u, hu_interval, rfl⟩
  have circle_data :=
    PolygonalReplacementCircularResidualPieceCircleData G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData i hcircular
  have hu_sphere :
      residualPieceData.edgeParam (residualPieceData.owner i) u ∈
        Metric.sphere c r := by
    exact circle_data.2.1 u
      (by simpa [sourceParam] using hsource_le_u)
      (by simpa [targetParam] using hu_lt_target.le)
  have hu_not_vertex_ball :
      ∀ v : V,
        residualPieceData.edgeParam (residualPieceData.owner i) u ∉
          Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v) := by
    intro v hu_vertex_ball
    exact
      (Set.disjoint_left.mp
        (residualPieceData.originalPiece_avoids_vertex_disk_interiors i v))
        hu_original hu_vertex_ball
  have hu_not_intersection_ball :
      ∀ x : {p // p ∈ D.intersectionPoints},
        residualPieceData.edgeParam (residualPieceData.owner i) u ∉
          Metric.ball x.1 (controlDisks.intersectionRadius x) := by
    intro x hu_intersection_ball
    exact
      (Set.disjoint_left.mp
        (residualPieceData.originalPiece_avoids_intersection_disk_interiors i x))
        hu_original hu_intersection_ball
  refine ⟨u, ?_, ?_, ?_, hu_original, hu_sphere, hu_not_vertex_ball,
    hu_not_intersection_ball⟩
  · simpa [sourceParam] using hsource_le_u
  · simpa [targetParam] using hu_lt_target
  · simpa [edgeParamAtOwner, e] using hu_ball
