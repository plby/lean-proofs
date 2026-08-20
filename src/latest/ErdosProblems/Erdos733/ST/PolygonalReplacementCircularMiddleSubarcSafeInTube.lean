import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualOriginalPieceClosedBallContactOnlyEndpoint

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementCircularMiddleSubarcSafeInTube]
lemma PolygonalReplacementCircularMiddleSubarcSafeInTube {V : Type u}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (residualPieceData :
      PolygonalReplacementResidualPieceData G D controlDisks boundaryPoints
        edgeEndpoints)
    (tube : residualPieceData.pieceIndex → Set (EuclideanSpace ℝ (Fin 2)))
    (_tube_open : ∀ i, IsOpen (tube i))
    (originalPiece_subset_tube :
      ∀ i, residualPieceData.originalPiece i ⊆ tube i)
    (i : residualPieceData.pieceIndex)
    {c : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {γ : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2)}
    (_hcircular :
      0 < r ∧
        Continuous γ ∧ Function.Injective γ ∧
        (∀ t, dist (γ t) c = r) ∧
        γ ⟨0, by simp⟩ = D.edgeSource (residualPieceData.owner i) ∧
        γ ⟨1, by simp⟩ = D.edgeTarget (residualPieceData.owner i) ∧
        D.edgeCarrier (residualPieceData.owner i) = Set.range γ ∧
        D.edgeRelativeInterior (residualPieceData.owner i) =
          Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
            γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩))
    (us ut : Set.Icc (0 : ℝ) 1)
    (hsource_us : residualPieceData.sourceParam i < us)
    (hus_ut : us < ut)
    (hut_target : ut < residualPieceData.targetParam i) :
    let middleImage : Set (EuclideanSpace ℝ (Fin 2)) :=
      residualPieceData.edgeParam (residualPieceData.owner i) '' Set.Icc us ut
    IsCompact middleImage ∧
      middleImage ⊆ tube i ∧
        residualPieceData.edgeParam (residualPieceData.owner i) us ∈
          middleImage ∧
          residualPieceData.edgeParam (residualPieceData.owner i) ut ∈
            middleImage ∧
            (∀ v : V,
              Disjoint middleImage
                (Metric.closedBall (D.vertexPlacement v)
                  (controlDisks.vertexRadius v))) ∧
              (∀ x : {p // p ∈ D.intersectionPoints},
                Disjoint middleImage
                  (Metric.closedBall x.1
                    (controlDisks.intersectionRadius x))) := by
-- BODY
  classical
  let middleImage : Set (EuclideanSpace ℝ (Fin 2)) :=
    residualPieceData.edgeParam (residualPieceData.owner i) '' Set.Icc us ut
  rcases residualPieceData.edgeParam_spec (residualPieceData.owner i) with
    ⟨hedge_cont, hedge_inj, _hsource, _htarget, _hcarrier, _hrel⟩
  have contact :=
    PolygonalReplacementResidualOriginalPieceClosedBallContactOnlyEndpoint G D
      controlDisks boundaryPoints edgeEndpoints residualPieceData
  have middle_subset_original :
      middleImage ⊆ residualPieceData.originalPiece i := by
    intro p hp
    rcases hp with ⟨u, hu, hpu⟩
    rw [residualPieceData.originalPiece_eq_parameter_interval i]
    refine ⟨u, ?_, hpu⟩
    exact ⟨le_trans hsource_us.le hu.1, le_trans hu.2 hut_target.le⟩
  have hcompact : IsCompact middleImage := by
    dsimp [middleImage]
    exact isCompact_Icc.image hedge_cont
  have hsubset_tube : middleImage ⊆ tube i := by
    intro p hp
    exact originalPiece_subset_tube i (middle_subset_original hp)
  have hsource_mem :
      residualPieceData.edgeParam (residualPieceData.owner i) us ∈
        middleImage := by
    exact ⟨us, ⟨le_rfl, hus_ut.le⟩, rfl⟩
  have htarget_mem :
      residualPieceData.edgeParam (residualPieceData.owner i) ut ∈
        middleImage := by
    exact ⟨ut, ⟨hus_ut.le, le_rfl⟩, rfl⟩
  have hvertex_disjoint :
      ∀ v : V,
        Disjoint middleImage
          (Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v)) := by
    intro v
    rw [Set.disjoint_left]
    intro p hpMiddle hpClosed
    rcases hpMiddle with ⟨u, hu, hpu⟩
    subst p
    have hpOriginal :
        residualPieceData.edgeParam (residualPieceData.owner i) u ∈
          residualPieceData.originalPiece i :=
      middle_subset_original ⟨u, hu, rfl⟩
    rcases contact.1 i v
        (residualPieceData.edgeParam (residualPieceData.owner i) u)
        hpOriginal hpClosed with
      ⟨h_eq_source, _hsource_sphere⟩ | ⟨h_eq_target, _htarget_sphere⟩
    · have hu_source : u = residualPieceData.sourceParam i :=
        hedge_inj (h_eq_source.trans (residualPieceData.source_eq_edgeParam i))
      have hsource_lt_u : residualPieceData.sourceParam i < u :=
        lt_of_lt_of_le hsource_us hu.1
      exact (lt_irrefl (residualPieceData.sourceParam i))
        (by simpa [hu_source] using hsource_lt_u)
    · have hu_target : u = residualPieceData.targetParam i :=
        hedge_inj (h_eq_target.trans (residualPieceData.target_eq_edgeParam i))
      have hu_lt_target : u < residualPieceData.targetParam i :=
        lt_of_le_of_lt hu.2 hut_target
      exact (lt_irrefl (residualPieceData.targetParam i))
        (by simpa [hu_target] using hu_lt_target)
  have hintersection_disjoint :
      ∀ x : {p // p ∈ D.intersectionPoints},
        Disjoint middleImage
          (Metric.closedBall x.1 (controlDisks.intersectionRadius x)) := by
    intro x
    rw [Set.disjoint_left]
    intro p hpMiddle hpClosed
    rcases hpMiddle with ⟨u, hu, hpu⟩
    subst p
    have hpOriginal :
        residualPieceData.edgeParam (residualPieceData.owner i) u ∈
          residualPieceData.originalPiece i :=
      middle_subset_original ⟨u, hu, rfl⟩
    rcases contact.2 i x
        (residualPieceData.edgeParam (residualPieceData.owner i) u)
        hpOriginal hpClosed with
      ⟨h_eq_source, _hsource_sphere⟩ | ⟨h_eq_target, _htarget_sphere⟩
    · have hu_source : u = residualPieceData.sourceParam i :=
        hedge_inj (h_eq_source.trans (residualPieceData.source_eq_edgeParam i))
      have hsource_lt_u : residualPieceData.sourceParam i < u :=
        lt_of_lt_of_le hsource_us hu.1
      exact (lt_irrefl (residualPieceData.sourceParam i))
        (by simpa [hu_source] using hsource_lt_u)
    · have hu_target : u = residualPieceData.targetParam i :=
        hedge_inj (h_eq_target.trans (residualPieceData.target_eq_edgeParam i))
      have hu_lt_target : u < residualPieceData.targetParam i :=
        lt_of_le_of_lt hu.2 hut_target
      exact (lt_irrefl (residualPieceData.targetParam i))
        (by simpa [hu_target] using hu_lt_target)
  exact ⟨hcompact, hsubset_tube, hsource_mem, htarget_mem,
    hvertex_disjoint, hintersection_disjoint⟩
