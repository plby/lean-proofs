import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualPieceData

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementCircularResidualPieceCircleData]
lemma PolygonalReplacementCircularResidualPieceCircleData {V : Type u}
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
    0 < r ∧
      (∀ t : Set.Icc (0 : ℝ) 1,
        residualPieceData.sourceParam i ≤ t →
          t ≤ residualPieceData.targetParam i →
            residualPieceData.edgeParam (residualPieceData.owner i) t ∈
              Metric.sphere c r) ∧
      residualPieceData.source i ∈ Metric.sphere c r ∧
        residualPieceData.target i ∈ Metric.sphere c r := by
-- BODY
  classical
  let e : G.edgeFinset := residualPieceData.owner i
  rcases hcircular with
    ⟨hr, _hγcont, _hγinj, hγcircle, _hγsource, _hγtarget,
      hγcarrier, _hγrel⟩
  rcases residualPieceData.edgeParam_spec e with
    ⟨_hedgeParam_cont, _hedgeParam_inj, _hedgeParam_source,
      _hedgeParam_target, hedgeParam_carrier, _hedgeParam_rel⟩
  have hγcarrier_e : D.edgeCarrier e = Set.range γ := by
    simpa [e] using hγcarrier
  have edgeParam_on_circle :
      ∀ t : Set.Icc (0 : ℝ) 1,
        residualPieceData.edgeParam e t ∈ Metric.sphere c r := by
    intro t
    have ht_carrier :
        residualPieceData.edgeParam e t ∈ D.edgeCarrier e := by
      rw [hedgeParam_carrier]
      exact ⟨t, rfl⟩
    have ht_range :
        residualPieceData.edgeParam e t ∈ Set.range γ := by
      simpa [hγcarrier_e] using ht_carrier
    rcases ht_range with ⟨s, hs⟩
    rw [Metric.mem_sphere]
    rw [← hs]
    exact hγcircle s
  refine ⟨hr, ?_, ?_, ?_⟩
  · intro t _ht_source _ht_target
    simpa [e] using edgeParam_on_circle t
  · have hsource := edgeParam_on_circle (residualPieceData.sourceParam i)
    simpa [e, residualPieceData.source_eq_edgeParam i] using hsource
  · have htarget := edgeParam_on_circle (residualPieceData.targetParam i)
    simpa [e, residualPieceData.target_eq_edgeParam i] using htarget
