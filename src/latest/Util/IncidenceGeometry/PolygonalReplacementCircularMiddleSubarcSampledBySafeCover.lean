import Util.IncidenceGeometry.PolygonalReplacementCircularMiddleSubarcFiniteSafeConvexCover
import Util.IncidenceGeometry.PolygonalReplacementCompactIntervalOpenCoverStrictSample

open Classical
noncomputable section

universe u

lemma PolygonalReplacementCircularMiddleSubarcSampledBySafeCover {V : Type u}
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
    (tube_open : ∀ i, IsOpen (tube i))
    (originalPiece_subset_tube :
      ∀ i, residualPieceData.originalPiece i ⊆ tube i)
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
            γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩))
    (us ut : Set.Icc (0 : ℝ) 1)
    (hsource_us : residualPieceData.sourceParam i < us)
    (hus_ut : us < ut)
    (hut_target : ut < residualPieceData.targetParam i) :
    let middleImage : Set (EuclideanSpace ℝ (Fin 2)) :=
      residualPieceData.edgeParam (residualPieceData.owner i) '' Set.Icc us ut
    ∃ centers : Finset middleImage,
      ∃ radius : middleImage → ℝ,
        middleImage ⊆ ⋃ z ∈ centers, Metric.ball z.1 (radius z) ∧
          (∀ z : middleImage, z ∈ centers → 0 < radius z) ∧
          (∀ z : middleImage, z ∈ centers →
            Convex ℝ (Metric.ball z.1 (radius z))) ∧
          (∀ z : middleImage, z ∈ centers →
            Metric.ball z.1 (radius z) ⊆ tube i) ∧
          (∀ z : middleImage, z ∈ centers → ∀ v : V,
            Disjoint (Metric.ball z.1 (radius z))
              (Metric.closedBall (D.vertexPlacement v)
                (controlDisks.vertexRadius v))) ∧
          (∀ z : middleImage, z ∈ centers →
            ∀ x : {p // p ∈ D.intersectionPoints},
              Disjoint (Metric.ball z.1 (radius z))
                (Metric.closedBall x.1
                  (controlDisks.intersectionRadius x))) ∧
          ∃ m : ℕ,
            ∃ params : Fin (m + 1) → Set.Icc (0 : ℝ) 1,
              ∃ centerFor :
                  Fin m → {z : middleImage // z ∈ centers},
                0 < m ∧
                  (∀ k : Fin (m + 1), params k ∈ Set.Icc us ut) ∧
                  params 0 = us ∧
                  params (Fin.last m) = ut ∧
                  (∀ n : Fin m,
                    params (Fin.castSucc n) < params (Fin.succ n)) ∧
                  (∀ n : Fin m, ∀ u : Set.Icc (0 : ℝ) 1,
                    u ∈ Set.Icc (params (Fin.castSucc n))
                        (params (Fin.succ n)) →
                      residualPieceData.edgeParam (residualPieceData.owner i) u ∈
                        Metric.ball (centerFor n).1.1
                          (radius (centerFor n).1)) := by
  classical
  let middleImage : Set (EuclideanSpace ℝ (Fin 2)) :=
    residualPieceData.edgeParam (residualPieceData.owner i) '' Set.Icc us ut
  rcases PolygonalReplacementCircularMiddleSubarcFiniteSafeConvexCover G D
      controlDisks boundaryPoints edgeEndpoints residualPieceData tube
      tube_open originalPiece_subset_tube i hcircular us ut hsource_us
      hus_ut hut_target with
    ⟨centers, radius, hcover, hpos, hconvex, htube, hvertex, hintersection⟩
  rcases residualPieceData.edgeParam_spec (residualPieceData.owner i) with
    ⟨hedge_cont, _hedge_inj, _hsource, _htarget, _hcarrier, _hrel⟩
  have hab : (us : ℝ) < (ut : ℝ) := hus_ut
  let toDomain : Set.Icc (us : ℝ) (ut : ℝ) → Set.Icc (0 : ℝ) 1 :=
    fun t => ⟨t.1, ⟨le_trans us.2.1 t.2.1, le_trans t.2.2 ut.2.2⟩⟩
  have toDomain_mem :
      ∀ t : Set.Icc (us : ℝ) (ut : ℝ), toDomain t ∈ Set.Icc us ut := by
    intro t
    exact ⟨t.2.1, t.2.2⟩
  have htoDomain_cont : Continuous toDomain := by
    exact Continuous.subtype_mk continuous_subtype_val
      (fun t => ⟨le_trans us.2.1 t.2.1, le_trans t.2.2 ut.2.2⟩)
  have hedge_restrict_cont :
      Continuous (fun t : Set.Icc (us : ℝ) (ut : ℝ) =>
        residualPieceData.edgeParam (residualPieceData.owner i)
          (toDomain t)) :=
    hedge_cont.comp htoDomain_cont
  let preimageCover :
      {z : middleImage // z ∈ centers} →
        Set (Set.Icc (us : ℝ) (ut : ℝ)) :=
    fun z =>
      {t | residualPieceData.edgeParam (residualPieceData.owner i)
          (toDomain t) ∈ Metric.ball z.1.1 (radius z.1)}
  have hpreimage_open :
      ∀ z : {z : middleImage // z ∈ centers}, IsOpen (preimageCover z) := by
    intro z
    dsimp [preimageCover]
    exact Metric.isOpen_ball.preimage hedge_restrict_cont
  have hpreimage_cover :
      Set.univ ⊆ ⋃ z : {z : middleImage // z ∈ centers}, preimageCover z := by
    intro t _ht
    have ht_middle :
        residualPieceData.edgeParam (residualPieceData.owner i) (toDomain t) ∈
          middleImage := by
      exact ⟨toDomain t, toDomain_mem t, rfl⟩
    have hcov := hcover ht_middle
    rcases Set.mem_iUnion.mp hcov with ⟨z, hzUnion⟩
    rcases Set.mem_iUnion.mp hzUnion with ⟨hzcenters, hzball⟩
    exact Set.mem_iUnion.mpr ⟨⟨z, hzcenters⟩, hzball⟩
  rcases PolygonalReplacementCompactIntervalOpenCoverStrictSample hab
      (c := preimageCover) hpreimage_open hpreimage_cover with
    ⟨m, realParams, hm_pos, hreal_start, hreal_end, hreal_strict,
      hreal_subinterval⟩
  let params : Fin (m + 1) → Set.Icc (0 : ℝ) 1 :=
    fun k => toDomain (realParams k)
  let centerFor : Fin m → {z : middleImage // z ∈ centers} :=
    fun n => Classical.choose (hreal_subinterval n)
  have hparams_mem :
      ∀ k : Fin (m + 1), params k ∈ Set.Icc us ut := by
    intro k
    exact toDomain_mem (realParams k)
  have hparams_start : params 0 = us := by
    apply Subtype.ext
    dsimp [params, toDomain]
    exact congrArg Subtype.val hreal_start
  have hparams_end : params (Fin.last m) = ut := by
    apply Subtype.ext
    dsimp [params, toDomain]
    exact congrArg Subtype.val hreal_end
  have hparams_strict :
      ∀ n : Fin m, params (Fin.castSucc n) < params (Fin.succ n) := by
    intro n
    rw [← Subtype.coe_lt_coe]
    dsimp [params, toDomain]
    exact hreal_strict n
  have hsubinterval :
      ∀ n : Fin m, ∀ u : Set.Icc (0 : ℝ) 1,
        u ∈ Set.Icc (params (Fin.castSucc n)) (params (Fin.succ n)) →
          residualPieceData.edgeParam (residualPieceData.owner i) u ∈
            Metric.ball (centerFor n).1.1 (radius (centerFor n).1) := by
    intro n u hu
    have hleft : (realParams (Fin.castSucc n) : ℝ) ≤ (u : ℝ) := by
      exact_mod_cast hu.1
    have hright : (u : ℝ) ≤ (realParams (Fin.succ n) : ℝ) := by
      exact_mod_cast hu.2
    let uReal : Set.Icc (us : ℝ) (ut : ℝ) :=
      ⟨u.1, ⟨le_trans (realParams (Fin.castSucc n)).2.1 hleft,
        le_trans hright (realParams (Fin.succ n)).2.2⟩⟩
    have huReal :
        uReal ∈ Set.Icc (realParams (Fin.castSucc n))
          (realParams (Fin.succ n)) := by
      exact ⟨hleft, hright⟩
    have hchosen := Classical.choose_spec (hreal_subinterval n)
    have hball := hchosen huReal
    have hdomain_eq : toDomain uReal = u := by
      apply Subtype.ext
      rfl
    simpa [centerFor, preimageCover, hdomain_eq] using hball
  exact ⟨centers, radius, hcover, hpos, hconvex, htube, hvertex,
    hintersection, m, params, centerFor, hm_pos, hparams_mem,
    hparams_start, hparams_end, hparams_strict, hsubinterval⟩
