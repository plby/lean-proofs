import Util.IncidenceGeometry.PolygonalReplacementCircularResidualPieceCircleData

open Classical
noncomputable section

universe u

lemma PolygonalReplacementCircularTargetEndpointCenterOrder {V : Type u}
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
        v = edgeEndpoints.edgeTargetVertex (residualPieceData.owner i) ∧
          residualPieceData.targetParam i =
            residualPieceData.targetBoundaryParam (residualPieceData.owner i) ∧
          residualPieceData.targetParam i <
            (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) ∧
          residualPieceData.edgeParam (residualPieceData.owner i)
              ⟨1, by simp⟩ =
            D.vertexPlacement v ∧
          residualPieceData.target i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
          residualPieceData.target i ∈
            D.edgeCarrier (residualPieceData.owner i) ∧
          D.vertexPlacement v ∈ Metric.sphere c r ∧
          residualPieceData.target i ∈ Metric.sphere c r) ∨
      (∃ x : {p // p ∈ D.intersectionPoints},
        ∃ hx : x.1 ∈ D.edgeRelativeInterior (residualPieceData.owner i),
          residualPieceData.target i =
              residualPieceData.edgeParam (residualPieceData.owner i)
                (residualPieceData.intersectionLeftParam hx) ∧
          residualPieceData.targetParam i =
              residualPieceData.intersectionLeftParam hx ∧
          residualPieceData.targetParam i <
              residualPieceData.intersectionCenterParam hx ∧
          residualPieceData.edgeParam (residualPieceData.owner i)
              (residualPieceData.intersectionCenterParam hx) = x.1 ∧
          x.1 ∈ Metric.sphere c r ∧
          residualPieceData.target i ∈ Metric.sphere c r ∧
          residualPieceData.target i ∈
            Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
          residualPieceData.target i ∈
            D.edgeCarrier (residualPieceData.owner i)) := by
  classical
  let e : G.edgeFinset := residualPieceData.owner i
  rcases hcircular with
    ⟨_hr, _hγcont, _hγinj, hγcircle, _hγsource, hγtarget,
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
  have hedge_target_circle :
      D.edgeTarget e ∈ Metric.sphere c r := by
    have hγtarget_e :
        γ ⟨1, by simp⟩ = D.edgeTarget e := by
      simpa [e] using hγtarget
    rw [Metric.mem_sphere]
    rw [← hγtarget_e]
    exact hγcircle ⟨1, by simp⟩
  rcases residualPieceData.target_endpoint_order i with hvertex | hintersection
  · rcases hvertex with
      ⟨htargetParam_eq, _htarget_eq_boundary, htarget_sphere,
        htarget_carrier⟩
    let v : V := edgeEndpoints.edgeTargetVertex e
    rcases residualPieceData.edgeParam_spec e with
      ⟨_hedge_cont, _hedge_inj, _hedge_source, hedge_target,
        _hedge_carrier, _hedge_rel⟩
    have hone_edge :
        residualPieceData.edgeParam e ⟨1, by simp⟩ =
          D.vertexPlacement v := by
      simpa [v] using
        hedge_target.trans (edgeEndpoints.edgeTarget_eq_vertexPlacement e)
    have htarget_ne_center :
        residualPieceData.target i ≠ D.vertexPlacement v := by
      intro htarget_eq_center
      have hdist :
          dist (residualPieceData.target i) (D.vertexPlacement v) =
            controlDisks.vertexRadius v := by
        simpa [Metric.mem_sphere, dist_eq_norm, v, e] using htarget_sphere
      rw [htarget_eq_center, dist_self] at hdist
      linarith [controlDisks.vertexRadius_pos v]
    have htargetParam_ne_one :
        residualPieceData.targetParam i ≠
          (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) := by
      intro hparam
      apply htarget_ne_center
      calc
        residualPieceData.target i =
            residualPieceData.edgeParam e (residualPieceData.targetParam i) :=
          by simpa [e] using residualPieceData.target_eq_edgeParam i
        _ = residualPieceData.edgeParam e ⟨1, by simp⟩ := by rw [hparam]
        _ = D.vertexPlacement v := hone_edge
    have htargetParam_lt_one :
        residualPieceData.targetParam i <
          (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) := by
      have htarget_le_one :
          residualPieceData.targetParam i ≤
            (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) := by
        exact (residualPieceData.targetParam i).2.2
      exact lt_of_le_of_ne htarget_le_one htargetParam_ne_one
    have hvertex_center_circle :
        D.vertexPlacement v ∈ Metric.sphere c r := by
      simpa [v, edgeEndpoints.edgeTarget_eq_vertexPlacement e] using
        hedge_target_circle
    have htarget_circle :
        residualPieceData.target i ∈ Metric.sphere c r :=
      hcarrier_circle (by simpa [e] using htarget_carrier)
    left
    refine ⟨v, rfl, ?_, htargetParam_lt_one, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [e] using htargetParam_eq
    · simpa [e] using hone_edge
    · simpa [e, v] using htarget_sphere
    · simpa [e] using htarget_carrier
    · exact hvertex_center_circle
    · exact htarget_circle
  · rcases hintersection with
      ⟨x, hx, htarget_eq_left, htargetParam_eq_left,
        htarget_lt_center, htarget_sphere, htarget_carrier⟩
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
    have htarget_circle :
        residualPieceData.target i ∈ Metric.sphere c r :=
      hcarrier_circle (by simpa [e] using htarget_carrier)
    right
    refine ⟨x, hx, ?_, ?_, ?_, ?_, hcenter_circle, htarget_circle, ?_, ?_⟩
    · simpa [e] using htarget_eq_left
    · simpa [e] using htargetParam_eq_left
    · simpa [e] using htarget_lt_center
    · simpa [e] using hcenter_eq
    · simpa [e] using htarget_sphere
    · simpa [e] using htarget_carrier
