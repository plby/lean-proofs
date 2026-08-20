import ErdosProblems.Erdos733.ST.PolygonalReplacementCircularEndpointChordPair
import ErdosProblems.Erdos733.ST.PolygonalReplacementCircularMiddleSubarcSampledBySafeCover
import ErdosProblems.Erdos733.ST.PolygonalReplacementCircularResidualPieceCircleData
import ErdosProblems.Erdos733.ST.PolygonalArcFromCircularOrderedSamples

open Classical
noncomputable section

universe u


-- [TABLET NODE: PolygonalReplacementCircularResidualPieceChainInTube]
lemma PolygonalReplacementCircularResidualPieceChainInTube {V : Type u}
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
            γ ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)) :
    ∃ Γ : PolygonalArc,
      Γ.source = residualPieceData.source i ∧
        Γ.target = residualPieceData.target i ∧
          Γ.carrier ⊆ tube i ∧
            (∀ v : V,
              Disjoint Γ.relativeInterior
                (Metric.ball (D.vertexPlacement v)
                  (controlDisks.vertexRadius v))) ∧
            (∀ x : {p // p ∈ D.intersectionPoints},
              Disjoint Γ.relativeInterior
                (Metric.ball x.1 (controlDisks.intersectionRadius x))) ∧
            (∀ v p,
              p ∈ Γ.carrier →
                p ∈ Metric.closedBall (D.vertexPlacement v)
                    (controlDisks.vertexRadius v) →
                  (p = residualPieceData.source i ∧
                      residualPieceData.source i ∈
                        Metric.sphere (D.vertexPlacement v)
                          (controlDisks.vertexRadius v)) ∨
                    (p = residualPieceData.target i ∧
                      residualPieceData.target i ∈
                        Metric.sphere (D.vertexPlacement v)
                          (controlDisks.vertexRadius v))) ∧
            (∀ x : {p // p ∈ D.intersectionPoints}, ∀ p,
              p ∈ Γ.carrier →
                p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) →
                  (p = residualPieceData.source i ∧
                      residualPieceData.source i ∈
                        Metric.sphere x.1
                          (controlDisks.intersectionRadius x)) ∨
                    (p = residualPieceData.target i ∧
                      residualPieceData.target i ∈
                        Metric.sphere x.1
                          (controlDisks.intersectionRadius x))) := by
-- BODY
  classical
  let e : G.edgeFinset := residualPieceData.owner i
  rcases residualPieceData.edgeParam_spec e with
    ⟨hedge_cont, hedge_inj, _hedge_source, _hedge_target,
      hedge_carrier, _hedge_rel⟩
  rcases hcircular with
    ⟨hr_pos, _hγ_cont, _hγ_inj, hγ_circle, _hγ_source, _hγ_target,
      hγ_carrier, _hγ_rel⟩
  have hγ_carrier_e : D.edgeCarrier e = Set.range γ := by
    simpa [e] using hγ_carrier
  have hedge_circle :
      ∀ t : Set.Icc (0 : ℝ) 1,
        dist (residualPieceData.edgeParam e t) c = r := by
    intro t
    have ht_carrier :
        residualPieceData.edgeParam e t ∈ D.edgeCarrier e := by
      rw [hedge_carrier]
      exact ⟨t, rfl⟩
    have ht_range : residualPieceData.edgeParam e t ∈ Set.range γ := by
      simpa [hγ_carrier_e] using ht_carrier
    rcases ht_range with ⟨s, hs⟩
    rw [← hs]
    exact hγ_circle s
  have _circleData :=
    PolygonalReplacementCircularResidualPieceCircleData G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData i
      (c := c) (r := r) (γ := γ)
      ⟨hr_pos, _hγ_cont, _hγ_inj, hγ_circle, _hγ_source, _hγ_target,
        hγ_carrier, _hγ_rel⟩
  rcases PolygonalReplacementCircularEndpointChordPair G D controlDisks
      boundaryPoints edgeEndpoints residualPieceData tube tube_open
      originalPiece_subset_tube i
      (c := c) (r := r) (γ := γ)
      ⟨hr_pos, _hγ_cont, _hγ_inj, hγ_circle, _hγ_source, _hγ_target,
        hγ_carrier, _hγ_rel⟩ with
    ⟨us, ut, hsource_us, hus_ut, hut_target, hsource_good, htarget_good⟩
  let middleImage : Set (EuclideanSpace ℝ (Fin 2)) :=
    residualPieceData.edgeParam (residualPieceData.owner i) '' Set.Icc us ut
  rcases PolygonalReplacementCircularMiddleSubarcSampledBySafeCover G D
      controlDisks boundaryPoints edgeEndpoints residualPieceData tube
      tube_open originalPiece_subset_tube i
      (c := c) (r := r) (γ := γ)
      ⟨hr_pos, _hγ_cont, _hγ_inj, hγ_circle, _hγ_source, _hγ_target,
        hγ_carrier, _hγ_rel⟩ us ut hsource_us hus_ut hut_target with
    ⟨centers, radius, _hcover, _hradius_pos, hconvex, hball_tube,
      hball_vertex_disjoint, hball_intersection_disjoint, m, params,
      centerFor, hm_pos, _hparams_mem, hparams_start, hparams_end,
      hparams_adjacent, hsubinterval⟩
  let baseParams : Fin (m + 2) → Set.Icc (0 : ℝ) 1 :=
    Fin.cons (residualPieceData.sourceParam i) params
  let fullParams : Fin (m + 3) → Set.Icc (0 : ℝ) 1 :=
    Fin.snoc baseParams (residualPieceData.targetParam i)
  have hfull_strict : StrictMono fullParams := by
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    refine Fin.lastCases ?last ?notLast k
    · have hleft :
          fullParams (Fin.last (m + 1)).castSucc = params (Fin.last m) := by
        simp [fullParams, baseParams]
      have hright :
          fullParams (Fin.last (m + 1 + 1)) =
            residualPieceData.targetParam i := by
        simp [fullParams, baseParams]
      simpa [hleft, hright, hparams_end] using hut_target
    · intro q
      refine Fin.cases ?sourceStep ?middleStep q
      · have hleft : fullParams 0 = residualPieceData.sourceParam i := by
          norm_num [fullParams, baseParams]
        have hright : fullParams 1 = params 0 := by
          have hidx :
              (1 : Fin (m + 3)) = Fin.castSucc (1 : Fin (m + 2)) := by
            ext
            rfl
          rw [hidx]
          show @Fin.snoc (m + 2) (fun _ => Set.Icc (0 : ℝ) 1) baseParams
              (residualPieceData.targetParam i)
              (Fin.castSucc (1 : Fin (m + 2))) = params 0
          rw [Fin.snoc_castSucc]
          show @Fin.cons (m + 1) (fun _ => Set.Icc (0 : ℝ) 1)
              (residualPieceData.sourceParam i) params (1 : Fin (m + 2)) =
            params 0
          rw [Fin.cons_one]
        simpa [hleft, hright, hparams_start] using hsource_us
      · intro n
        have hleft :
            fullParams n.castSucc.castSucc.succ = params (Fin.castSucc n) := by
          show @Fin.snoc (m + 2) (fun _ => Set.Icc (0 : ℝ) 1) baseParams
              (residualPieceData.targetParam i)
              (n.castSucc.castSucc.succ) = params (Fin.castSucc n)
          rw [Fin.succ_castSucc (i := n.castSucc), Fin.snoc_castSucc]
          show @Fin.cons (m + 1) (fun _ => Set.Icc (0 : ℝ) 1)
              (residualPieceData.sourceParam i) params
              (n.castSucc.succ) = params (Fin.castSucc n)
          rw [Fin.cons_succ]
        have hright :
            fullParams n.castSucc.succ.succ = params (Fin.succ n) := by
          show @Fin.snoc (m + 2) (fun _ => Set.Icc (0 : ℝ) 1) baseParams
              (residualPieceData.targetParam i)
              (n.castSucc.succ.succ) = params (Fin.succ n)
          rw [Fin.succ_castSucc (i := n), Fin.succ_castSucc (i := n.succ),
            Fin.snoc_castSucc]
          show @Fin.cons (m + 1) (fun _ => Set.Icc (0 : ℝ) 1)
              (residualPieceData.sourceParam i) params
              (n.succ.succ) = params (Fin.succ n)
          rw [Fin.cons_succ]
        simpa [hleft, hright] using hparams_adjacent n
  let Γ : PolygonalArc :=
    PolygonalArcFromCircularOrderedSamples (m := m + 2) (by omega)
      (c := c) (r := r)
      (γ := residualPieceData.edgeParam e) hedge_cont hedge_inj
      hedge_circle fullParams
      (fun {a b} hab => hfull_strict hab)
  have hfull_zero : fullParams 0 = residualPieceData.sourceParam i := by
    norm_num [fullParams, baseParams]
  have hfull_one : fullParams 1 = us := by
    have hright : fullParams 1 = params 0 := by
      have hidx :
          (1 : Fin (m + 3)) = Fin.castSucc (1 : Fin (m + 2)) := by
        ext
        rfl
      rw [hidx]
      show @Fin.snoc (m + 2) (fun _ => Set.Icc (0 : ℝ) 1) baseParams
          (residualPieceData.targetParam i)
          (Fin.castSucc (1 : Fin (m + 2))) = params 0
      rw [Fin.snoc_castSucc]
      show @Fin.cons (m + 1) (fun _ => Set.Icc (0 : ℝ) 1)
          (residualPieceData.sourceParam i) params (1 : Fin (m + 2)) =
        params 0
      rw [Fin.cons_one]
    simp [hright, hparams_start]
  have hfull_penultimate :
      fullParams ⟨m + 1, by omega⟩ = ut := by
    have hleft :
        fullParams (Fin.last (m + 1)).castSucc = params (Fin.last m) := by
      simp [fullParams, baseParams]
    have hidx :
        (⟨m + 1, by omega⟩ : Fin (m + 3)) =
          (Fin.last (m + 1)).castSucc := by
      ext
      simp
    simpa [hidx, hparams_end] using hleft
  have hfull_last :
      fullParams ⟨m + 2, by omega⟩ = residualPieceData.targetParam i := by
    have hlast :
        fullParams (Fin.last (m + 2)) = residualPieceData.targetParam i := by
      simp [fullParams, baseParams]
    have hidx :
        (⟨m + 2, by omega⟩ : Fin (m + 3)) = Fin.last (m + 2) := by
      ext
      simp
    simpa [hidx] using hlast
  have hfull_middle_left :
      ∀ k : Fin m,
        fullParams ⟨k.1 + 1, by omega⟩ = params (Fin.castSucc k) := by
    intro k
    have h :
        fullParams k.castSucc.castSucc.succ = params (Fin.castSucc k) := by
      show @Fin.snoc (m + 2) (fun _ => Set.Icc (0 : ℝ) 1) baseParams
          (residualPieceData.targetParam i)
          (k.castSucc.castSucc.succ) = params (Fin.castSucc k)
      rw [Fin.succ_castSucc (i := k.castSucc), Fin.snoc_castSucc]
      show @Fin.cons (m + 1) (fun _ => Set.Icc (0 : ℝ) 1)
          (residualPieceData.sourceParam i) params
          (k.castSucc.succ) = params (Fin.castSucc k)
      rw [Fin.cons_succ]
    have hidx :
        (⟨k.1 + 1, by omega⟩ : Fin (m + 3)) =
          k.castSucc.castSucc.succ := by
      ext
      simp
    simpa [hidx] using h
  have hfull_middle_right :
      ∀ k : Fin m,
        fullParams ⟨k.1 + 2, by omega⟩ = params (Fin.succ k) := by
    intro k
    have h :
        fullParams k.castSucc.succ.succ = params (Fin.succ k) := by
      show @Fin.snoc (m + 2) (fun _ => Set.Icc (0 : ℝ) 1) baseParams
          (residualPieceData.targetParam i)
          (k.castSucc.succ.succ) = params (Fin.succ k)
      rw [Fin.succ_castSucc (i := k), Fin.succ_castSucc (i := k.succ),
        Fin.snoc_castSucc]
      show @Fin.cons (m + 1) (fun _ => Set.Icc (0 : ℝ) 1)
          (residualPieceData.sourceParam i) params
          (k.succ.succ) = params (Fin.succ k)
      rw [Fin.cons_succ]
    have hidx :
        (⟨k.1 + 2, by omega⟩ : Fin (m + 3)) =
          k.castSucc.succ.succ := by
      ext
      simp
    simpa [hidx] using h
  have hΓ_source : Γ.source = residualPieceData.source i := by
    simpa [Γ, PolygonalArcFromCircularOrderedSamples, e, hfull_zero]
      using (residualPieceData.source_eq_edgeParam i).symm
  have hΓ_target : Γ.target = residualPieceData.target i := by
    simpa [Γ, PolygonalArcFromCircularOrderedSamples, e, hfull_last]
      using (residualPieceData.target_eq_edgeParam i).symm
  have hsource_segment_tube :
      segment ℝ (residualPieceData.source i)
          (residualPieceData.edgeParam e us) ⊆ tube i := by
    rcases hsource_good with
      ⟨v, _hv_owner, _hv_sphere, _hv_carrier, hb_tube, hseg_tube,
        _hcontact, _hopen, _hothers, _hintersections⟩ |
      ⟨x, _hx_rel, _hx_sphere, _hx_carrier, hb_tube, hseg_tube,
        _hcontact, _hopen, _hvertices, _hothers⟩
    · simpa [e] using hseg_tube
    · simpa [e] using hseg_tube
  have htarget_segment_tube :
      segment ℝ (residualPieceData.edgeParam e ut)
          (residualPieceData.target i) ⊆ tube i := by
    rcases htarget_good with
      ⟨v, _hv_owner, _hv_sphere, _hv_carrier, hb_tube, hseg_tube,
        _hcontact, _hopen, _hothers, _hintersections⟩ |
      ⟨x, _hx_rel, _hx_sphere, _hx_carrier, hb_tube, hseg_tube,
        _hcontact, _hopen, _hvertices, _hothers⟩
    · intro p hp
      exact hseg_tube (by simpa [e, segment_symm] using hp)
    · intro p hp
      exact hseg_tube (by simpa [e, segment_symm] using hp)
  have hmiddle_segment_ball :
      ∀ k : Fin m,
        segment ℝ
            (residualPieceData.edgeParam e (params (Fin.castSucc k)))
            (residualPieceData.edgeParam e (params (Fin.succ k))) ⊆
          Metric.ball (centerFor k).1.1 (radius (centerFor k).1) := by
    intro k
    have hleft :
        residualPieceData.edgeParam e (params (Fin.castSucc k)) ∈
          Metric.ball (centerFor k).1.1 (radius (centerFor k).1) := by
      have hmem :
          params (Fin.castSucc k) ∈
            Set.Icc (params (Fin.castSucc k)) (params (Fin.succ k)) :=
        ⟨le_rfl, (hparams_adjacent k).le⟩
      simpa [e] using hsubinterval k (params (Fin.castSucc k)) hmem
    have hright :
        residualPieceData.edgeParam e (params (Fin.succ k)) ∈
          Metric.ball (centerFor k).1.1 (radius (centerFor k).1) := by
      have hmem :
          params (Fin.succ k) ∈
            Set.Icc (params (Fin.castSucc k)) (params (Fin.succ k)) :=
        ⟨(hparams_adjacent k).le, le_rfl⟩
      simpa [e] using hsubinterval k (params (Fin.succ k)) hmem
    exact (hconvex (centerFor k).1 (centerFor k).2).segment_subset hleft hright
  have hmiddle_segment_tube :
      ∀ k : Fin m,
        segment ℝ
            (residualPieceData.edgeParam e (params (Fin.castSucc k)))
            (residualPieceData.edgeParam e (params (Fin.succ k))) ⊆
          tube i := by
    intro k p hp
    exact hball_tube (centerFor k).1 (centerFor k).2
      (hmiddle_segment_ball k hp)
  have hmiddle_segment_vertex_disjoint :
      ∀ k : Fin m, ∀ v : V,
        Disjoint
          (segment ℝ
            (residualPieceData.edgeParam e (params (Fin.castSucc k)))
            (residualPieceData.edgeParam e (params (Fin.succ k))))
          (Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v)) := by
    intro k v
    rw [Set.disjoint_left]
    intro p hp hpClosed
    exact
      (Set.disjoint_left.mp
        (hball_vertex_disjoint (centerFor k).1 (centerFor k).2 v))
        (hmiddle_segment_ball k hp) hpClosed
  have hmiddle_segment_intersection_disjoint :
      ∀ k : Fin m, ∀ x : {p // p ∈ D.intersectionPoints},
        Disjoint
          (segment ℝ
            (residualPieceData.edgeParam e (params (Fin.castSucc k)))
            (residualPieceData.edgeParam e (params (Fin.succ k))))
          (Metric.closedBall x.1 (controlDisks.intersectionRadius x)) := by
    intro k x
    rw [Set.disjoint_left]
    intro p hp hpClosed
    exact
      (Set.disjoint_left.mp
        (hball_intersection_disjoint (centerFor k).1 (centerFor k).2 x))
        (hmiddle_segment_ball k hp) hpClosed
  have hsource_segment_vertex_contact :
      ∀ v p,
        p ∈ segment ℝ (residualPieceData.source i)
            (residualPieceData.edgeParam e us) →
        p ∈ Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v) →
          p = residualPieceData.source i ∧
            residualPieceData.source i ∈
              Metric.sphere (D.vertexPlacement v)
                (controlDisks.vertexRadius v) := by
    intro v p hpseg hpClosed
    rcases hsource_good with
      ⟨v0, _hv_owner, hv_sphere, _hv_carrier, _hb_tube, _hseg_tube,
        hcontact, _hopen, hother_vertices, _hintersections⟩ |
      ⟨x0, _hx_rel, _hx_sphere, _hx_carrier, _hb_tube, _hseg_tube,
        _hcontact, _hopen, hall_vertices, _hother_intersections⟩
    · by_cases hv : v = v0
      · subst v
        exact ⟨hcontact p (by simpa [e] using hpseg) hpClosed, hv_sphere⟩
      · exfalso
        exact (Set.disjoint_left.mp (hother_vertices v hv))
          (by simpa [e] using hpseg) hpClosed
    · exfalso
      exact (Set.disjoint_left.mp (hall_vertices v))
        (by simpa [e] using hpseg) hpClosed
  have hsource_segment_intersection_contact :
      ∀ x : {p // p ∈ D.intersectionPoints}, ∀ p,
        p ∈ segment ℝ (residualPieceData.source i)
            (residualPieceData.edgeParam e us) →
        p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) →
          p = residualPieceData.source i ∧
            residualPieceData.source i ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
    intro x p hpseg hpClosed
    rcases hsource_good with
      ⟨v0, _hv_owner, _hv_sphere, _hv_carrier, _hb_tube, _hseg_tube,
        _hcontact, _hopen, _hother_vertices, hall_intersections⟩ |
      ⟨x0, _hx_rel, hx_sphere, _hx_carrier, _hb_tube, _hseg_tube,
        hcontact, _hopen, _hall_vertices, hother_intersections⟩
    · exfalso
      exact (Set.disjoint_left.mp (hall_intersections x))
        (by simpa [e] using hpseg) hpClosed
    · by_cases hx : x = x0
      · subst x
        exact ⟨hcontact p (by simpa [e] using hpseg) hpClosed, hx_sphere⟩
      · exfalso
        exact (Set.disjoint_left.mp (hother_intersections x hx))
          (by simpa [e] using hpseg) hpClosed
  have htarget_segment_vertex_contact :
      ∀ v p,
        p ∈ segment ℝ (residualPieceData.edgeParam e ut)
            (residualPieceData.target i) →
        p ∈ Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v) →
          p = residualPieceData.target i ∧
            residualPieceData.target i ∈
              Metric.sphere (D.vertexPlacement v)
                (controlDisks.vertexRadius v) := by
    intro v p hpseg hpClosed
    rcases htarget_good with
      ⟨v0, _hv_owner, hv_sphere, _hv_carrier, _hb_tube, _hseg_tube,
        hcontact, _hopen, hother_vertices, _hintersections⟩ |
      ⟨x0, _hx_rel, _hx_sphere, _hx_carrier, _hb_tube, _hseg_tube,
        _hcontact, _hopen, hall_vertices, _hother_intersections⟩
    · by_cases hv : v = v0
      · subst v
        exact ⟨hcontact p (by simpa [e, segment_symm] using hpseg) hpClosed,
          hv_sphere⟩
      · exfalso
        exact (Set.disjoint_left.mp (hother_vertices v hv))
          (by simpa [e, segment_symm] using hpseg) hpClosed
    · exfalso
      exact (Set.disjoint_left.mp (hall_vertices v))
        (by simpa [e, segment_symm] using hpseg) hpClosed
  have htarget_segment_intersection_contact :
      ∀ x : {p // p ∈ D.intersectionPoints}, ∀ p,
        p ∈ segment ℝ (residualPieceData.edgeParam e ut)
            (residualPieceData.target i) →
        p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) →
          p = residualPieceData.target i ∧
            residualPieceData.target i ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
    intro x p hpseg hpClosed
    rcases htarget_good with
      ⟨v0, _hv_owner, _hv_sphere, _hv_carrier, _hb_tube, _hseg_tube,
        _hcontact, _hopen, _hother_vertices, hall_intersections⟩ |
      ⟨x0, _hx_rel, hx_sphere, _hx_carrier, _hb_tube, _hseg_tube,
        hcontact, _hopen, _hall_vertices, hother_intersections⟩
    · exfalso
      exact (Set.disjoint_left.mp (hall_intersections x))
        (by simpa [e, segment_symm] using hpseg) hpClosed
    · by_cases hx : x = x0
      · subst x
        exact ⟨hcontact p (by simpa [e, segment_symm] using hpseg) hpClosed,
          hx_sphere⟩
      · exfalso
        exact (Set.disjoint_left.mp (hother_intersections x hx))
          (by simpa [e, segment_symm] using hpseg) hpClosed
  have hcarrier_cases :
      ∀ {p : EuclideanSpace ℝ (Fin 2)}, p ∈ Γ.carrier →
        p ∈ segment ℝ (residualPieceData.source i)
            (residualPieceData.edgeParam e us) ∨
        (∃ k : Fin m,
          p ∈ segment ℝ
            (residualPieceData.edgeParam e (params (Fin.castSucc k)))
            (residualPieceData.edgeParam e (params (Fin.succ k)))) ∨
        p ∈ segment ℝ (residualPieceData.edgeParam e ut)
            (residualPieceData.target i) := by
    intro p hp
    rw [Γ.carrier_eq] at hp
    rcases hp with ⟨n, hn, hpseg⟩
    have hlen : Γ.vertices.length = m + 3 := by
      simp [Γ, PolygonalArcFromCircularOrderedSamples]
    have hn_bound : n + 1 < m + 3 := by
      simpa [hlen] using hn
    have hvertices :
        Γ.vertices =
          List.ofFn (fun j : Fin (m + 3) =>
            residualPieceData.edgeParam e (fullParams j)) := by
      simp [Γ, PolygonalArcFromCircularOrderedSamples]
    by_cases hn0 : n = 0
    · subst n
      left
      simpa [Γ, PolygonalArcFromCircularOrderedSamples, e, hfull_zero,
        hfull_one, residualPieceData.source_eq_edgeParam i] using hpseg
    · by_cases hnlast : n = m + 1
      · subst n
        right
        right
        have hv_left :
            Γ.vertices[m + 1] = residualPieceData.edgeParam e ut := by
          have hget :
              Γ.vertices[m + 1] =
                residualPieceData.edgeParam e
                  (fullParams ⟨m + 1, by omega⟩) := by
            simpa [Γ, PolygonalArcFromCircularOrderedSamples] using
              (List.getElem_ofFn
              (f := fun j : Fin (m + 3) =>
                residualPieceData.edgeParam e (fullParams j))
              (i := m + 1) (h := by simp))
          simpa [hfull_penultimate] using hget
        have hv_right :
            Γ.vertices[m + 2] = residualPieceData.target i := by
          have hget :
              Γ.vertices[m + 2] =
                residualPieceData.edgeParam e
                  (fullParams ⟨m + 2, by omega⟩) := by
            simpa [Γ, PolygonalArcFromCircularOrderedSamples] using
              (List.getElem_ofFn
              (f := fun j : Fin (m + 3) =>
                residualPieceData.edgeParam e (fullParams j))
              (i := m + 2) (h := by simp))
          simpa [e, hfull_last, residualPieceData.target_eq_edgeParam i]
            using hget
        simpa [hv_left, hv_right] using hpseg
      · right
        left
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hn_le_m : n ≤ m := by omega
        let k : Fin m := ⟨n - 1, by omega⟩
        refine ⟨k, ?_⟩
        have hidx_left :
            (⟨n, by omega⟩ : Fin (m + 3)) =
              (⟨k.1 + 1, by omega⟩ : Fin (m + 3)) := by
          ext
          dsimp [k]
          omega
        have hidx_right :
            (⟨n + 1, by omega⟩ : Fin (m + 3)) =
              (⟨k.1 + 2, by omega⟩ : Fin (m + 3)) := by
          ext
          dsimp [k]
          omega
        have hv_left :
            Γ.vertices[n] =
              residualPieceData.edgeParam e (params (Fin.castSucc k)) := by
          have hget :
              Γ.vertices[n] =
                residualPieceData.edgeParam e
                  (fullParams ⟨n, by omega⟩) := by
            simpa [Γ, PolygonalArcFromCircularOrderedSamples] using
              (List.getElem_ofFn
              (f := fun j : Fin (m + 3) =>
                residualPieceData.edgeParam e (fullParams j))
              (i := n) (h := by simp; omega))
          simpa [hidx_left, hfull_middle_left k] using hget
        have hv_right :
            Γ.vertices[n + 1] =
              residualPieceData.edgeParam e (params (Fin.succ k)) := by
          have hget :
              Γ.vertices[n + 1] =
                residualPieceData.edgeParam e
                  (fullParams ⟨n + 1, by omega⟩) := by
            simpa [Γ, PolygonalArcFromCircularOrderedSamples] using
              (List.getElem_ofFn
              (f := fun j : Fin (m + 3) =>
                residualPieceData.edgeParam e (fullParams j))
              (i := n + 1) (h := by simp; omega))
          simpa [hidx_right, hfull_middle_right k] using hget
        simpa [hv_left, hv_right] using hpseg
  have hcarrier_subset_tube : Γ.carrier ⊆ tube i := by
    intro p hp
    rcases hcarrier_cases hp with hpSource | hrest
    · exact hsource_segment_tube hpSource
    · rcases hrest with ⟨k, hpMiddle⟩ | hpTarget
      · exact hmiddle_segment_tube k hpMiddle
      · exact htarget_segment_tube hpTarget
  have hvertex_closed_contact :
      ∀ v p,
        p ∈ Γ.carrier →
          p ∈ Metric.closedBall (D.vertexPlacement v)
              (controlDisks.vertexRadius v) →
            (p = residualPieceData.source i ∧
                residualPieceData.source i ∈
                  Metric.sphere (D.vertexPlacement v)
                    (controlDisks.vertexRadius v)) ∨
              (p = residualPieceData.target i ∧
                residualPieceData.target i ∈
                  Metric.sphere (D.vertexPlacement v)
                    (controlDisks.vertexRadius v)) := by
    intro v p hpCarrier hpClosed
    rcases hcarrier_cases hpCarrier with hpSource | hrest
    · exact Or.inl (hsource_segment_vertex_contact v p hpSource hpClosed)
    · rcases hrest with ⟨k, hpMiddle⟩ | hpTarget
      · exfalso
        exact
          (Set.disjoint_left.mp (hmiddle_segment_vertex_disjoint k v))
          hpMiddle hpClosed
      · exact Or.inr (htarget_segment_vertex_contact v p hpTarget hpClosed)
  have hintersection_closed_contact :
      ∀ x : {p // p ∈ D.intersectionPoints}, ∀ p,
        p ∈ Γ.carrier →
          p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) →
            (p = residualPieceData.source i ∧
                residualPieceData.source i ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x)) ∨
              (p = residualPieceData.target i ∧
                residualPieceData.target i ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x)) := by
    intro x p hpCarrier hpClosed
    rcases hcarrier_cases hpCarrier with hpSource | hrest
    · exact Or.inl (hsource_segment_intersection_contact x p hpSource hpClosed)
    · rcases hrest with ⟨k, hpMiddle⟩ | hpTarget
      · exfalso
        exact
          (Set.disjoint_left.mp (hmiddle_segment_intersection_disjoint k x))
          hpMiddle hpClosed
      · exact Or.inr (htarget_segment_intersection_contact x p hpTarget hpClosed)
  have hrel_subset_carrier :
      Γ.relativeInterior ⊆ Γ.carrier := by
    intro p hp
    have hp' : p ∈ Γ.carrier \ ({Γ.source, Γ.target} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
      simpa [Γ.relativeInterior_eq] using hp
    exact hp'.1
  have hrel_ne_source :
      ∀ {p}, p ∈ Γ.relativeInterior → p ≠ residualPieceData.source i := by
    intro p hp hps
    have hp' : p ∈ Γ.carrier \ ({Γ.source, Γ.target} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
      simpa [Γ.relativeInterior_eq] using hp
    exact hp'.2 (by simp [hΓ_source, hps])
  have hrel_ne_target :
      ∀ {p}, p ∈ Γ.relativeInterior → p ≠ residualPieceData.target i := by
    intro p hp hpt
    have hp' : p ∈ Γ.carrier \ ({Γ.source, Γ.target} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
      simpa [Γ.relativeInterior_eq] using hp
    exact hp'.2 (by simp [hΓ_target, hpt])
  have hrel_vertex_disjoint :
      ∀ v : V,
        Disjoint Γ.relativeInterior
          (Metric.ball (D.vertexPlacement v)
            (controlDisks.vertexRadius v)) := by
    intro v
    rw [Set.disjoint_left]
    intro p hpRel hpBall
    have hpClosed :
        p ∈ Metric.closedBall (D.vertexPlacement v)
            (controlDisks.vertexRadius v) := by
      rw [Metric.mem_closedBall]
      exact le_of_lt (by simpa [Metric.mem_ball] using hpBall)
    rcases hvertex_closed_contact v p (hrel_subset_carrier hpRel) hpClosed with
      ⟨hps, _hsphere⟩ | ⟨hpt, _hsphere⟩
    · exact hrel_ne_source hpRel hps
    · exact hrel_ne_target hpRel hpt
  have hrel_intersection_disjoint :
      ∀ x : {p // p ∈ D.intersectionPoints},
        Disjoint Γ.relativeInterior
          (Metric.ball x.1 (controlDisks.intersectionRadius x)) := by
    intro x
    rw [Set.disjoint_left]
    intro p hpRel hpBall
    have hpClosed :
        p ∈ Metric.closedBall x.1 (controlDisks.intersectionRadius x) := by
      rw [Metric.mem_closedBall]
      exact le_of_lt (by simpa [Metric.mem_ball] using hpBall)
    rcases hintersection_closed_contact x p (hrel_subset_carrier hpRel) hpClosed with
      ⟨hps, _hsphere⟩ | ⟨hpt, _hsphere⟩
    · exact hrel_ne_source hpRel hps
    · exact hrel_ne_target hpRel hpt
  refine ⟨Γ, hΓ_source, hΓ_target, hcarrier_subset_tube,
    hrel_vertex_disjoint, hrel_intersection_disjoint, ?_, ?_⟩
  · intro v p hpCarrier hpClosed
    exact hvertex_closed_contact v p hpCarrier hpClosed
  · intro x p hpCarrier hpClosed
    exact hintersection_closed_contact x p hpCarrier hpClosed
