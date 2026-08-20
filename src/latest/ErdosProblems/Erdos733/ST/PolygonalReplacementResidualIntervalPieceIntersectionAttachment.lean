import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualIntervalPieceExactIntersectionGaps

open Classical
noncomputable section

universe u


-- [TABLET NODE: PolygonalReplacementResidualIntervalPieceIntersectionAttachment]
lemma PolygonalReplacementResidualIntervalPieceIntersectionAttachment {V : Type u}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (edgeParam :
      (e : G.edgeFinset) → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (sourceBoundaryParam targetBoundaryParam :
      G.edgeFinset → Set.Icc (0 : ℝ) 1)
    (intersectionCenterParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (intersectionLeftParam intersectionRightParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (intersection_cut_boundary :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e),
          edgeParam e (intersectionLeftParam hx) ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
            edgeParam e (intersectionLeftParam hx) ∈ D.edgeCarrier e ∧
              edgeParam e (intersectionRightParam hx) ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                edgeParam e (intersectionRightParam hx) ∈ D.edgeCarrier e ∧
                  edgeParam e (intersectionLeftParam hx) ≠
                    edgeParam e (intersectionRightParam hx))
    (intersection_cut_boundary_exhaustive :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
          (hx : x.1 ∈ D.edgeRelativeInterior e)
          {p : EuclideanSpace ℝ (Fin 2)},
          p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
            p ∈ D.edgeCarrier e →
              p = edgeParam e (intersectionLeftParam hx) ∨
                p = edgeParam e (intersectionRightParam hx))
    (S : PolygonalReplacementResidualPieceSkeletonData G D
      sourceBoundaryParam targetBoundaryParam intersectionCenterParam
      intersectionLeftParam intersectionRightParam)
    (B : PolygonalReplacementResidualIntervalPieceBasicData G D controlDisks
        boundaryPoints edgeEndpoints)
    (pieceEquiv : B.pieceIndex ≃ S.pieceIndex)
    (B_owner_eq_skeleton :
      ∀ i : B.pieceIndex, B.owner i = S.owner (pieceEquiv i))
    (B_sourceParam_eq_skeleton :
      ∀ i : B.pieceIndex, B.sourceParam i = S.sourceParam (pieceEquiv i))
    (B_targetParam_eq_skeleton :
      ∀ i : B.pieceIndex, B.targetParam i = S.targetParam (pieceEquiv i))
    (B_source_eq_skeleton :
      ∀ i : B.pieceIndex,
        B.source i =
          edgeParam (S.owner (pieceEquiv i)) (S.sourceParam (pieceEquiv i)))
    (B_target_eq_skeleton :
      ∀ i : B.pieceIndex,
        B.target i =
          edgeParam (S.owner (pieceEquiv i)) (S.targetParam (pieceEquiv i)))
    (B_edgePieceOrder_eq_skeleton :
      ∀ e : G.edgeFinset,
        (B.edgePieceOrder e).map (fun i => pieceEquiv i) =
          S.edgePieceOrder e)
    (first_source_boundary :
      ∀ e i,
        (B.edgePieceOrder e).head? = some i →
          B.source i = edgeEndpoints.sourceBoundaryPoint e ∧
            B.source i ∈
                Metric.sphere (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
                  (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) ∧
              B.source i ∈ D.edgeCarrier e)
    (last_target_boundary :
      ∀ e i,
        (B.edgePieceOrder e).getLast? = some i →
          B.target i = edgeEndpoints.targetBoundaryPoint e ∧
            B.target i ∈
                Metric.sphere (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
                  (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) ∧
              B.target i ∈ D.edgeCarrier e) :
    ∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e p⦄,
      x.1 ∈ D.edgeRelativeInterior e →
        p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
          p ∈ D.edgeCarrier e →
            ∃! i : B.pieceIndex, B.owner i = e ∧
              (B.source i = p ∨ B.target i = p) := by
-- BODY
  classical
  obtain ⟨consecutive_gap, between_gap⟩ :=
    PolygonalReplacementResidualIntervalPieceExactIntersectionGaps G D
      controlDisks boundaryPoints edgeEndpoints edgeParam
      sourceBoundaryParam targetBoundaryParam intersectionCenterParam
      intersectionLeftParam intersectionRightParam S B pieceEquiv
      B_owner_eq_skeleton B_sourceParam_eq_skeleton
      B_targetParam_eq_skeleton B_source_eq_skeleton B_target_eq_skeleton
      B_edgePieceOrder_eq_skeleton
  have vertex_intersection_contradiction :
      ∀ (v : V) (x : {p // p ∈ D.intersectionPoints})
        {q : EuclideanSpace ℝ (Fin 2)},
        q ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
          q ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) → False := by
    intro v x q hv hx
    have hdis := controlDisks.vertex_intersection_disjoint v x
    exact (Set.disjoint_left.mp hdis)
      (Metric.sphere_subset_closedBall hv) (Metric.sphere_subset_closedBall hx)
  have common_intersection_boundary_center :
      ∀ {x c : {p // p ∈ D.intersectionPoints}}
        {q : EuclideanSpace ℝ (Fin 2)},
        q ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
          q ∈ Metric.sphere c.1 (controlDisks.intersectionRadius c) →
            c = x := by
    intro x c q hx hc
    by_contra hne
    have hdis := controlDisks.intersection_intersection_disjoint
      (x := c) (y := x) hne
    exact (Set.disjoint_left.mp hdis)
      (Metric.sphere_subset_closedBall hc) (Metric.sphere_subset_closedBall hx)
  have cut_index_eq :
      ∀ {e : G.edgeFinset}
        {a b : {x : {p // p ∈ D.intersectionPoints} //
          x.1 ∈ D.edgeRelativeInterior e}} {m n : ℕ},
        (S.cutList e)[m]? = some a →
          (S.cutList e)[n]? = some b → a = b → m = n := by
    intro e a b m n hma hnb hab
    rcases (List.getElem?_eq_some_iff.mp hma) with ⟨hm, hma'⟩
    rcases (List.getElem?_eq_some_iff.mp hnb) with ⟨hn, hnb'⟩
    have hget : (S.cutList e)[m] = (S.cutList e)[n] := by
      rw [hma', hnb', hab]
    exact (List.Nodup.getElem_inj_iff (S.cutList_nodup e)).mp hget
  have locate_owned :
      ∀ {e : G.edgeFinset} {j : B.pieceIndex}, B.owner j = e →
        ∃ k, ∃ hk : k < (B.edgePieceOrder e).length,
          (B.edgePieceOrder e)[k] = j := by
    intro e j howner
    have hmem : j ∈ B.edgePieceOrder e :=
      (B.edgePieceOrder_owner_iff e j).2 howner
    exact (List.mem_iff_getElem.mp hmem)
  intro x e p hx hpSphere hpCarrier
  rcases between_gap x e hx with
    ⟨n, hn, hcut_between, htarget_left, hsource_right,
      _htargetParam_left, _hsourceParam_right, _hleft_center,
      _hcenter_right⟩
  have hn0 : n < (B.edgePieceOrder e).length := Nat.lt_of_succ_lt hn
  have hn1 : n + 1 < (B.edgePieceOrder e).length := hn
  have howner_left :
      B.owner ((B.edgePieceOrder e)[n]) = e := by
    have hmem : (B.edgePieceOrder e)[n] ∈ B.edgePieceOrder e :=
      List.getElem_mem hn0
    exact (B.edgePieceOrder_owner_iff e ((B.edgePieceOrder e)[n])).1 hmem
  have howner_right :
      B.owner ((B.edgePieceOrder e)[n + 1]) = e := by
    have hmem : (B.edgePieceOrder e)[n + 1] ∈ B.edgePieceOrder e :=
      List.getElem_mem hn1
    exact (B.edgePieceOrder_owner_iff e ((B.edgePieceOrder e)[n + 1])).1 hmem
  rcases intersection_cut_boundary_exhaustive hx hpSphere hpCarrier with
    hp_left | hp_right
  · have left_unique :
        ∀ j : B.pieceIndex, B.owner j = e →
          (B.source j = p ∨ B.target j = p) →
            j = (B.edgePieceOrder e)[n] := by
      intro j hownerj hj_endpoint
      rcases locate_owned hownerj with ⟨k, hk, hget⟩
      rcases hj_endpoint with hsourcej | htargetj
      · by_cases hk0 : k = 0
        · exfalso
          have hhead : (B.edgePieceOrder e).head? = some j := by
            subst hk0
            rw [List.head?_eq_getElem?]
            simpa [List.getElem?_eq_getElem hk] using congrArg some hget
          have hfirst := first_source_boundary e j hhead
          have hvertex :
              B.source j ∈
                Metric.sphere
                  (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
                  (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) :=
            hfirst.2.1
          have hintersection :
              B.source j ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
            rw [hsourcej]
            exact hpSphere
          exact vertex_intersection_contradiction
            (edgeEndpoints.edgeSourceVertex e) x hvertex hintersection
        · exfalso
          rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨m, rfl⟩
          have hsucc : m + 1 < (B.edgePieceOrder e).length := by
            simpa [Nat.succ_eq_add_one] using hk
          have hget_succ : (B.edgePieceOrder e)[m + 1] = j := by
            simpa [Nat.succ_eq_add_one] using hget
          rcases consecutive_gap e m hsucc with
            ⟨c, _hcget, _htarget_m, hsource_m1, _htargetParam_m,
              _hsourceParam_m1, _hleft_center_c, _hcenter_right_c⟩
          have hp_right_c :
              p = edgeParam e (intersectionRightParam c.2) := by
            calc
              p = B.source j := hsourcej.symm
              _ = B.source ((B.edgePieceOrder e)[m + 1]) := by
                rw [hget_succ]
              _ = edgeParam e (intersectionRightParam c.2) := hsource_m1
          have hpSphere_c :
              p ∈ Metric.sphere c.1.1 (controlDisks.intersectionRadius c.1) := by
            rw [hp_right_c]
            exact (intersection_cut_boundary c.2).2.2.1
          have hc_eq_x :
              c.1 = x :=
            common_intersection_boundary_center hpSphere hpSphere_c
          have hc_eq :
              c = (⟨x, hx⟩ :
                {x : {p // p ∈ D.intersectionPoints} //
                  x.1 ∈ D.edgeRelativeInterior e}) := Subtype.ext hc_eq_x
          have hp_right_x :
              p = edgeParam e (intersectionRightParam hx) := by
            simpa [hc_eq] using hp_right_c
          exact (intersection_cut_boundary hx).2.2.2.2
            (hp_left.symm.trans hp_right_x)
      · by_cases hlast_index : k + 1 = (B.edgePieceOrder e).length
        · exfalso
          have hlast : (B.edgePieceOrder e).getLast? = some j := by
            rw [List.getLast?_eq_getElem?]
            have hidx : (B.edgePieceOrder e).length - 1 = k := by omega
            have hlast_lt :
                (B.edgePieceOrder e).length - 1 <
                  (B.edgePieceOrder e).length := by omega
            rw [List.getElem?_eq_getElem hlast_lt]
            simpa [hidx] using congrArg some hget
          have hlast_data := last_target_boundary e j hlast
          have hvertex :
              B.target j ∈
                Metric.sphere
                  (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
                  (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) :=
            hlast_data.2.1
          have hintersection :
              B.target j ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
            rw [htargetj]
            exact hpSphere
          exact vertex_intersection_contradiction
            (edgeEndpoints.edgeTargetVertex e) x hvertex hintersection
        · have hsucc : k + 1 < (B.edgePieceOrder e).length := by omega
          rcases consecutive_gap e k hsucc with
            ⟨c, hcget, htarget_k, _hsource_k1, _htargetParam_k,
              _hsourceParam_k1, _hleft_center_c, _hcenter_right_c⟩
          have hp_left_c :
              p = edgeParam e (intersectionLeftParam c.2) := by
            calc
              p = B.target j := htargetj.symm
              _ = B.target ((B.edgePieceOrder e)[k]) := by
                rw [hget]
              _ = edgeParam e (intersectionLeftParam c.2) := htarget_k
          have hpSphere_c :
              p ∈ Metric.sphere c.1.1 (controlDisks.intersectionRadius c.1) := by
            rw [hp_left_c]
            exact (intersection_cut_boundary c.2).1
          have hc_eq_x :
              c.1 = x :=
            common_intersection_boundary_center hpSphere hpSphere_c
          have hc_eq :
              c = (⟨x, hx⟩ :
                {x : {p // p ∈ D.intersectionPoints} //
                  x.1 ∈ D.edgeRelativeInterior e}) := Subtype.ext hc_eq_x
          have hkn : k = n :=
            cut_index_eq hcget hcut_between hc_eq
          subst hkn
          exact hget.symm
    refine ⟨(B.edgePieceOrder e)[n], ?_, ?_⟩
    · exact ⟨howner_left, Or.inr (htarget_left.trans hp_left.symm)⟩
    · intro j hj
      exact left_unique j hj.1 hj.2
  · have right_unique :
        ∀ j : B.pieceIndex, B.owner j = e →
          (B.source j = p ∨ B.target j = p) →
            j = (B.edgePieceOrder e)[n + 1] := by
      intro j hownerj hj_endpoint
      rcases locate_owned hownerj with ⟨k, hk, hget⟩
      rcases hj_endpoint with hsourcej | htargetj
      · by_cases hk0 : k = 0
        · exfalso
          have hhead : (B.edgePieceOrder e).head? = some j := by
            subst hk0
            rw [List.head?_eq_getElem?]
            simpa [List.getElem?_eq_getElem hk] using congrArg some hget
          have hfirst := first_source_boundary e j hhead
          have hvertex :
              B.source j ∈
                Metric.sphere
                  (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
                  (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) :=
            hfirst.2.1
          have hintersection :
              B.source j ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
            rw [hsourcej]
            exact hpSphere
          exact vertex_intersection_contradiction
            (edgeEndpoints.edgeSourceVertex e) x hvertex hintersection
        · rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨m, rfl⟩
          have hsucc : m + 1 < (B.edgePieceOrder e).length := by
            simpa [Nat.succ_eq_add_one] using hk
          have hget_succ : (B.edgePieceOrder e)[m + 1] = j := by
            simpa [Nat.succ_eq_add_one] using hget
          rcases consecutive_gap e m hsucc with
            ⟨c, hcget, _htarget_m, hsource_m1, _htargetParam_m,
              _hsourceParam_m1, _hleft_center_c, _hcenter_right_c⟩
          have hp_right_c :
              p = edgeParam e (intersectionRightParam c.2) := by
            calc
              p = B.source j := hsourcej.symm
              _ = B.source ((B.edgePieceOrder e)[m + 1]) := by
                rw [hget_succ]
              _ = edgeParam e (intersectionRightParam c.2) := hsource_m1
          have hpSphere_c :
              p ∈ Metric.sphere c.1.1 (controlDisks.intersectionRadius c.1) := by
            rw [hp_right_c]
            exact (intersection_cut_boundary c.2).2.2.1
          have hc_eq_x :
              c.1 = x :=
            common_intersection_boundary_center hpSphere hpSphere_c
          have hc_eq :
              c = (⟨x, hx⟩ :
                {x : {p // p ∈ D.intersectionPoints} //
                  x.1 ∈ D.edgeRelativeInterior e}) := Subtype.ext hc_eq_x
          have hmn : m = n :=
            cut_index_eq hcget hcut_between hc_eq
          subst hmn
          exact hget_succ.symm
      · by_cases hlast_index : k + 1 = (B.edgePieceOrder e).length
        · exfalso
          have hlast : (B.edgePieceOrder e).getLast? = some j := by
            rw [List.getLast?_eq_getElem?]
            have hidx : (B.edgePieceOrder e).length - 1 = k := by omega
            have hlast_lt :
                (B.edgePieceOrder e).length - 1 <
                  (B.edgePieceOrder e).length := by omega
            rw [List.getElem?_eq_getElem hlast_lt]
            simpa [hidx] using congrArg some hget
          have hlast_data := last_target_boundary e j hlast
          have hvertex :
              B.target j ∈
                Metric.sphere
                  (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
                  (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) :=
            hlast_data.2.1
          have hintersection :
              B.target j ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
            rw [htargetj]
            exact hpSphere
          exact vertex_intersection_contradiction
            (edgeEndpoints.edgeTargetVertex e) x hvertex hintersection
        · exfalso
          have hsucc : k + 1 < (B.edgePieceOrder e).length := by omega
          rcases consecutive_gap e k hsucc with
            ⟨c, _hcget, htarget_k, _hsource_k1, _htargetParam_k,
              _hsourceParam_k1, _hleft_center_c, _hcenter_right_c⟩
          have hp_left_c :
              p = edgeParam e (intersectionLeftParam c.2) := by
            calc
              p = B.target j := htargetj.symm
              _ = B.target ((B.edgePieceOrder e)[k]) := by
                rw [hget]
              _ = edgeParam e (intersectionLeftParam c.2) := htarget_k
          have hpSphere_c :
              p ∈ Metric.sphere c.1.1 (controlDisks.intersectionRadius c.1) := by
            rw [hp_left_c]
            exact (intersection_cut_boundary c.2).1
          have hc_eq_x :
              c.1 = x :=
            common_intersection_boundary_center hpSphere hpSphere_c
          have hc_eq :
              c = (⟨x, hx⟩ :
                {x : {p // p ∈ D.intersectionPoints} //
                  x.1 ∈ D.edgeRelativeInterior e}) := Subtype.ext hc_eq_x
          have hp_left_x :
              p = edgeParam e (intersectionLeftParam hx) := by
            simpa [hc_eq] using hp_left_c
          exact (intersection_cut_boundary hx).2.2.2.2
            (hp_left_x.symm.trans hp_right)
    refine ⟨(B.edgePieceOrder e)[n + 1], ?_, ?_⟩
    · exact ⟨howner_right, Or.inl (hsource_right.trans hp_right.symm)⟩
    · intro j hj
      exact right_unique j hj.1 hj.2
