import Util.IncidenceGeometry.PolygonalReplacementCircularResidualPieceCircleData

open Classical
noncomputable section

universe u

lemma PolygonalReplacementCircularSourceEndpointCenterOrder {V : Type u}
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
    (∃ v : V,
        v = edgeEndpoints.edgeSourceVertex (residualPieceData.owner i) ∧
          residualPieceData.sourceParam i =
            residualPieceData.sourceBoundaryParam (residualPieceData.owner i) ∧
          (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) <
            residualPieceData.sourceParam i ∧
          residualPieceData.edgeParam (residualPieceData.owner i)
              ⟨0, by simp⟩ =
            D.vertexPlacement v ∧
          residualPieceData.source i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
          residualPieceData.source i ∈
            D.edgeCarrier (residualPieceData.owner i) ∧
          D.vertexPlacement v ∈ Metric.sphere c r ∧
          residualPieceData.source i ∈ Metric.sphere c r) ∨
      (∃ x : {p // p ∈ D.intersectionPoints},
        ∃ hx : x.1 ∈ D.edgeRelativeInterior (residualPieceData.owner i),
          residualPieceData.source i =
              residualPieceData.edgeParam (residualPieceData.owner i)
                (residualPieceData.intersectionRightParam hx) ∧
          residualPieceData.sourceParam i =
              residualPieceData.intersectionRightParam hx ∧
          residualPieceData.intersectionCenterParam hx <
              residualPieceData.sourceParam i ∧
          residualPieceData.edgeParam (residualPieceData.owner i)
              (residualPieceData.intersectionCenterParam hx) = x.1 ∧
          x.1 ∈ Metric.sphere c r ∧
          residualPieceData.source i ∈ Metric.sphere c r ∧
          residualPieceData.source i ∈
            Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
          residualPieceData.source i ∈
            D.edgeCarrier (residualPieceData.owner i)) := by
  classical
  let e : G.edgeFinset := residualPieceData.owner i
  rcases hcircular with
    ⟨_hr, _hγcont, _hγinj, hγcircle, hγsource, _hγtarget,
      hγcarrier, _hγrel⟩
  have hcarrier_circle :
      ∀ {p : EuclideanSpace ℝ (Fin 2)},
        p ∈ D.edgeCarrier e → p ∈ Metric.sphere c r := by
    intro p hp
    have hcarrier_e : D.edgeCarrier e = Set.range γ := by
      simpa [e] using hγcarrier
    rw [hcarrier_e] at hp
    rcases hp with ⟨t, rfl⟩
    rw [Metric.mem_sphere]
    exact hγcircle t
  have hedge_source_circle :
      D.edgeSource e ∈ Metric.sphere c r := by
    have hγsource_e :
        γ ⟨0, by simp⟩ = D.edgeSource e := by
      simpa [e] using hγsource
    rw [Metric.mem_sphere]
    rw [← hγsource_e]
    exact hγcircle ⟨0, by simp⟩
  rcases residualPieceData.source_endpoint_order i with hvertex | hintersection
  · rcases hvertex with
      ⟨hsourceParam_eq, _hsource_eq_boundary, hsource_sphere,
        hsource_carrier⟩
    let v : V := edgeEndpoints.edgeSourceVertex e
    rcases residualPieceData.edgeParam_spec e with
      ⟨_hedge_cont, _hedge_inj, hedge_source, _hedge_target,
        _hedge_carrier, _hedge_rel⟩
    have hzero_edge :
        residualPieceData.edgeParam e ⟨0, by simp⟩ =
          D.vertexPlacement v := by
      simpa [v] using
        hedge_source.trans (edgeEndpoints.edgeSource_eq_vertexPlacement e)
    have hsource_ne_center :
        residualPieceData.source i ≠ D.vertexPlacement v := by
      intro hsource_eq_center
      have hdist :
          dist (residualPieceData.source i) (D.vertexPlacement v) =
            controlDisks.vertexRadius v := by
        simpa [Metric.mem_sphere, dist_eq_norm, v, e] using hsource_sphere
      rw [hsource_eq_center, dist_self] at hdist
      linarith [controlDisks.vertexRadius_pos v]
    have hsourceParam_ne_zero :
        residualPieceData.sourceParam i ≠
          (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) := by
      intro hparam
      apply hsource_ne_center
      calc
        residualPieceData.source i =
            residualPieceData.edgeParam e (residualPieceData.sourceParam i) :=
          by simpa [e] using residualPieceData.source_eq_edgeParam i
        _ = residualPieceData.edgeParam e ⟨0, by simp⟩ := by rw [hparam]
        _ = D.vertexPlacement v := hzero_edge
    have hzero_lt_sourceParam :
        (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) <
          residualPieceData.sourceParam i := by
      have hzero_le :
          (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) ≤
            residualPieceData.sourceParam i := by
        exact (residualPieceData.sourceParam i).2.1
      exact lt_of_le_of_ne hzero_le (Ne.symm hsourceParam_ne_zero)
    have hvertex_center_circle :
        D.vertexPlacement v ∈ Metric.sphere c r := by
      simpa [v, edgeEndpoints.edgeSource_eq_vertexPlacement e] using
        hedge_source_circle
    have hsource_circle :
        residualPieceData.source i ∈ Metric.sphere c r :=
      hcarrier_circle (by simpa [e] using hsource_carrier)
    left
    refine ⟨v, rfl, ?_, hzero_lt_sourceParam, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [e] using hsourceParam_eq
    · simpa [e] using hzero_edge
    · simpa [e, v] using hsource_sphere
    · simpa [e] using hsource_carrier
    · exact hvertex_center_circle
    · exact hsource_circle
  · rcases hintersection with
      ⟨x, hx, hsource_eq_right, hsourceParam_eq_right,
        hcenter_lt_source, hsource_sphere, hsource_carrier⟩
    have hcenter_eq :
        residualPieceData.edgeParam e
            (residualPieceData.intersectionCenterParam hx) = x.1 := by
      simpa [e] using residualPieceData.intersectionCenterParam_eq hx
    have hcenter_carrier : x.1 ∈ D.edgeCarrier e := by
      rcases residualPieceData.edgeParam_spec e with
        ⟨_hedge_cont, _hedge_inj, _hedge_source, _hedge_target,
          hedge_carrier, _hedge_rel⟩
      rw [← hcenter_eq, hedge_carrier]
      exact ⟨residualPieceData.intersectionCenterParam hx, rfl⟩
    have hcenter_circle : x.1 ∈ Metric.sphere c r :=
      hcarrier_circle hcenter_carrier
    have hsource_circle :
        residualPieceData.source i ∈ Metric.sphere c r :=
      hcarrier_circle (by simpa [e] using hsource_carrier)
    right
    refine ⟨x, hx, ?_, ?_, ?_, ?_, hcenter_circle, hsource_circle, ?_, ?_⟩
    · simpa [e] using hsource_eq_right
    · simpa [e] using hsourceParam_eq_right
    · simpa [e] using hcenter_lt_source
    · simpa [e] using hcenter_eq
    · simpa [e] using hsource_sphere
    · simpa [e] using hsource_carrier
