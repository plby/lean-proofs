import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualIntervalPieceControlComplement

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementResidualIntervalPieceBoundaryFields]
lemma PolygonalReplacementResidualIntervalPieceBoundaryFields {V : Type u}
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
    (sourceBoundaryParam_eq :
      ∀ e, edgeParam e (sourceBoundaryParam e) =
        edgeEndpoints.sourceBoundaryPoint e)
    (targetBoundaryParam_eq :
      ∀ e, edgeParam e (targetBoundaryParam e) =
        edgeEndpoints.targetBoundaryPoint e)
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
          S.edgePieceOrder e) :
    (∀ e i,
      (B.edgePieceOrder e).head? = some i →
        B.source i = edgeEndpoints.sourceBoundaryPoint e ∧
          B.source i ∈
              Metric.sphere (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
                (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) ∧
            B.source i ∈ D.edgeCarrier e) ∧
      (∀ e i,
        (B.edgePieceOrder e).getLast? = some i →
          B.target i = edgeEndpoints.targetBoundaryPoint e ∧
            B.target i ∈
                Metric.sphere (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
                  (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) ∧
              B.target i ∈ D.edgeCarrier e) ∧
        (∀ e n (hn : n + 1 < (B.edgePieceOrder e).length),
          ∃ x : {p // p ∈ D.intersectionPoints},
            ∃ hx : x.1 ∈ D.edgeRelativeInterior e,
              B.target ((B.edgePieceOrder e)[n]) ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                B.source ((B.edgePieceOrder e)[n + 1]) ∈
                    Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                  B.targetParam ((B.edgePieceOrder e)[n]) <
                      intersectionCenterParam hx ∧
                    intersectionCenterParam hx <
                      B.sourceParam ((B.edgePieceOrder e)[n + 1])) ∧
          (∀ (x : {p // p ∈ D.intersectionPoints}) (e : G.edgeFinset)
            (hx : x.1 ∈ D.edgeRelativeInterior e),
              ∃ n, ∃ hn : n + 1 < (B.edgePieceOrder e).length,
                B.targetParam ((B.edgePieceOrder e)[n]) <
                    intersectionCenterParam hx ∧
                  intersectionCenterParam hx <
                    B.sourceParam ((B.edgePieceOrder e)[n + 1])) ∧
            (∀ e n (hn : n + 1 < (B.edgePieceOrder e).length),
              ∃ x : {p // p ∈ D.intersectionPoints},
                x.1 ∈ D.edgeRelativeInterior e ∧
                  B.target ((B.edgePieceOrder e)[n]) ∈
                      Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                    B.target ((B.edgePieceOrder e)[n]) ∈ D.edgeCarrier e ∧
                      B.source ((B.edgePieceOrder e)[n + 1]) ∈
                          Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                        B.source ((B.edgePieceOrder e)[n + 1]) ∈ D.edgeCarrier e ∧
                          B.target ((B.edgePieceOrder e)[n]) ≠
                            B.source ((B.edgePieceOrder e)[n + 1])) ∧
              (∀ (x : {p // p ∈ D.intersectionPoints}) (e : G.edgeFinset),
                x.1 ∈ D.edgeRelativeInterior e →
                  ∃ n, ∃ hn : n + 1 < (B.edgePieceOrder e).length,
                    B.target ((B.edgePieceOrder e)[n]) ∈
                        Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                      B.target ((B.edgePieceOrder e)[n]) ∈ D.edgeCarrier e ∧
                        B.source ((B.edgePieceOrder e)[n + 1]) ∈
                            Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                          B.source ((B.edgePieceOrder e)[n + 1]) ∈ D.edgeCarrier e ∧
                            B.target ((B.edgePieceOrder e)[n]) ≠
                              B.source ((B.edgePieceOrder e)[n + 1])) := by
-- BODY
  classical
  have first_source_boundary :
      ∀ e i,
        (B.edgePieceOrder e).head? = some i →
          B.source i = edgeEndpoints.sourceBoundaryPoint e ∧
            B.source i ∈
                Metric.sphere (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
                  (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) ∧
              B.source i ∈ D.edgeCarrier e := by
    intro e i hhead
    have hmemOpt : i ∈ (B.edgePieceOrder e).head? := by
      simpa [hhead]
    have hmem : i ∈ B.edgePieceOrder e := List.mem_of_mem_head? hmemOpt
    have hownerB : B.owner i = e := (B.edgePieceOrder_owner_iff e i).1 hmem
    have hownerS : S.owner (pieceEquiv i) = e := by
      rwa [B_owner_eq_skeleton i] at hownerB
    have hheadS : (S.edgePieceOrder e).head? = some (pieceEquiv i) := by
      rw [← B_edgePieceOrder_eq_skeleton e]
      simp [hhead]
    have hsourceParamS :
        S.sourceParam (pieceEquiv i) = sourceBoundaryParam e :=
      S.edgePieceOrder_first_sourceParam e (pieceEquiv i) hheadS
    have hsource_eq : B.source i = edgeEndpoints.sourceBoundaryPoint e := by
      calc
        B.source i =
            edgeParam (S.owner (pieceEquiv i)) (S.sourceParam (pieceEquiv i)) :=
          B_source_eq_skeleton i
        _ = edgeParam e (sourceBoundaryParam e) := by
          rw [hownerS, hsourceParamS]
        _ = edgeEndpoints.sourceBoundaryPoint e := sourceBoundaryParam_eq e
    refine ⟨hsource_eq, ?_, ?_⟩
    · rw [hsource_eq]
      exact (edgeEndpoints.sourceBoundary_on_control_boundary e).1
    · rw [hsource_eq]
      exact (edgeEndpoints.sourceBoundary_on_control_boundary e).2
  have last_target_boundary :
      ∀ e i,
        (B.edgePieceOrder e).getLast? = some i →
          B.target i = edgeEndpoints.targetBoundaryPoint e ∧
            B.target i ∈
                Metric.sphere (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
                  (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) ∧
              B.target i ∈ D.edgeCarrier e := by
    intro e i hlast
    have hmemOpt : i ∈ (B.edgePieceOrder e).getLast? := by
      simpa [hlast]
    have hmem : i ∈ B.edgePieceOrder e := List.mem_of_mem_getLast? hmemOpt
    have hownerB : B.owner i = e := (B.edgePieceOrder_owner_iff e i).1 hmem
    have hownerS : S.owner (pieceEquiv i) = e := by
      rwa [B_owner_eq_skeleton i] at hownerB
    have hlastS : (S.edgePieceOrder e).getLast? = some (pieceEquiv i) := by
      rw [← B_edgePieceOrder_eq_skeleton e]
      simpa [hlast]
    have htargetParamS :
        S.targetParam (pieceEquiv i) = targetBoundaryParam e :=
      S.edgePieceOrder_last_targetParam e (pieceEquiv i) hlastS
    have htarget_eq : B.target i = edgeEndpoints.targetBoundaryPoint e := by
      calc
        B.target i =
            edgeParam (S.owner (pieceEquiv i)) (S.targetParam (pieceEquiv i)) :=
          B_target_eq_skeleton i
        _ = edgeParam e (targetBoundaryParam e) := by
          rw [hownerS, htargetParamS]
        _ = edgeEndpoints.targetBoundaryPoint e := targetBoundaryParam_eq e
    refine ⟨htarget_eq, ?_, ?_⟩
    · rw [htarget_eq]
      exact (edgeEndpoints.targetBoundary_on_control_boundary e).1
    · rw [htarget_eq]
      exact (edgeEndpoints.targetBoundary_on_control_boundary e).2
  have consecutive_gap :
      ∀ e n (hn : n + 1 < (B.edgePieceOrder e).length),
        ∃ x : {p // p ∈ D.intersectionPoints},
          ∃ hx : x.1 ∈ D.edgeRelativeInterior e,
            B.target ((B.edgePieceOrder e)[n]) =
                edgeParam e (intersectionLeftParam hx) ∧
              B.source ((B.edgePieceOrder e)[n + 1]) =
                  edgeParam e (intersectionRightParam hx) ∧
                B.targetParam ((B.edgePieceOrder e)[n]) =
                    intersectionLeftParam hx ∧
                  B.sourceParam ((B.edgePieceOrder e)[n + 1]) =
                      intersectionRightParam hx ∧
                    intersectionLeftParam hx < intersectionCenterParam hx ∧
                      intersectionCenterParam hx < intersectionRightParam hx := by
    intro e n hn
    have hlenS : (S.edgePieceOrder e).length = (B.edgePieceOrder e).length := by
      rw [← B_edgePieceOrder_eq_skeleton e, List.length_map]
    have hnS : n + 1 < (S.edgePieceOrder e).length := by
      rwa [hlenS]
    have hn0S : n < (S.edgePieceOrder e).length := Nat.lt_of_succ_lt hnS
    have hn1S : n + 1 < (S.edgePieceOrder e).length := hnS
    have hcutn : n < (S.cutList e).length := by
      have htmp : n + 1 < (S.cutList e).length + 1 := by
        simpa [S.edgePieceOrder_length_eq_retainedIntervals_length e,
          S.retainedIntervals_length_eq_cutList_length e] using hnS
      omega
    let c := (S.cutList e)[n]
    have hmatch := S.edgePieceOrder_matches_retainedIntervals e n hn0S
    have htarget_map : (S.retainedIntervals e)[n]?.map Prod.snd =
        some (S.targetParam ((S.edgePieceOrder e)[n])) := by
      rw [hmatch]
      rfl
    have hsource_match := S.edgePieceOrder_matches_retainedIntervals e (n + 1) hn1S
    have hsource_map : (S.retainedIntervals e)[n + 1]?.map Prod.fst =
        some (S.sourceParam ((S.edgePieceOrder e)[n + 1])) := by
      rw [hsource_match]
      rfl
    have hgap := S.retainedIntervals_cut_gap e n hcutn
    have hS_target :
        S.targetParam ((S.edgePieceOrder e)[n]) =
          intersectionLeftParam ((S.cutList e)[n].2) := by
      rw [hgap.1] at htarget_map
      exact Option.some.inj htarget_map.symm
    have hS_source :
        S.sourceParam ((S.edgePieceOrder e)[n + 1]) =
          intersectionRightParam ((S.cutList e)[n].2) := by
      rw [hgap.2.1] at hsource_map
      exact Option.some.inj hsource_map.symm
    have hleft_center :
        intersectionLeftParam ((S.cutList e)[n].2) <
          intersectionCenterParam ((S.cutList e)[n].2) := hgap.2.2.1
    have hcenter_right :
        intersectionCenterParam ((S.cutList e)[n].2) <
          intersectionRightParam ((S.cutList e)[n].2) := hgap.2.2.2
    have hn0B : n < (B.edgePieceOrder e).length := Nat.lt_of_succ_lt hn
    have hn1B : n + 1 < (B.edgePieceOrder e).length := hn
    have hmap_n :
        pieceEquiv ((B.edgePieceOrder e)[n]) = (S.edgePieceOrder e)[n] := by
      have hget := congrArg (fun l : List S.pieceIndex => l[n]?)
        (B_edgePieceOrder_eq_skeleton e)
      have hget' :
          some (pieceEquiv ((B.edgePieceOrder e)[n])) =
            some ((S.edgePieceOrder e)[n]) := by
        simpa [List.getElem?_map, List.getElem?_eq_getElem, hn0B, hn0S] using hget
      exact Option.some.inj hget'
    have hmap_n1 :
        pieceEquiv ((B.edgePieceOrder e)[n + 1]) =
          (S.edgePieceOrder e)[n + 1] := by
      have hget := congrArg (fun l : List S.pieceIndex => l[n + 1]?)
        (B_edgePieceOrder_eq_skeleton e)
      have hget' :
          some (pieceEquiv ((B.edgePieceOrder e)[n + 1])) =
            some ((S.edgePieceOrder e)[n + 1]) := by
        simpa [List.getElem?_map, List.getElem?_eq_getElem, hn1B, hn1S] using hget
      exact Option.some.inj hget'
    have howner_n :
        S.owner (pieceEquiv ((B.edgePieceOrder e)[n])) = e := by
      have hmem : (B.edgePieceOrder e)[n] ∈ B.edgePieceOrder e :=
        List.getElem_mem hn0B
      have hownerB : B.owner ((B.edgePieceOrder e)[n]) = e :=
        (B.edgePieceOrder_owner_iff e ((B.edgePieceOrder e)[n])).1 hmem
      rwa [B_owner_eq_skeleton] at hownerB
    have howner_n1 :
        S.owner (pieceEquiv ((B.edgePieceOrder e)[n + 1])) = e := by
      have hmem : (B.edgePieceOrder e)[n + 1] ∈ B.edgePieceOrder e :=
        List.getElem_mem hn1B
      have hownerB : B.owner ((B.edgePieceOrder e)[n + 1]) = e :=
        (B.edgePieceOrder_owner_iff e ((B.edgePieceOrder e)[n + 1])).1 hmem
      rwa [B_owner_eq_skeleton] at hownerB
    have hS_target_B :
        S.targetParam (pieceEquiv ((B.edgePieceOrder e)[n])) =
          intersectionLeftParam ((S.cutList e)[n].2) := by
      rwa [hmap_n]
    have hS_source_B :
        S.sourceParam (pieceEquiv ((B.edgePieceOrder e)[n + 1])) =
          intersectionRightParam ((S.cutList e)[n].2) := by
      rwa [hmap_n1]
    have hB_targetParam :
        B.targetParam ((B.edgePieceOrder e)[n]) =
          intersectionLeftParam ((S.cutList e)[n].2) := by
      rw [B_targetParam_eq_skeleton, hS_target_B]
    have hB_sourceParam :
        B.sourceParam ((B.edgePieceOrder e)[n + 1]) =
          intersectionRightParam ((S.cutList e)[n].2) := by
      rw [B_sourceParam_eq_skeleton, hS_source_B]
    have hB_target :
        B.target ((B.edgePieceOrder e)[n]) =
          edgeParam e (intersectionLeftParam ((S.cutList e)[n].2)) := by
      rw [B_target_eq_skeleton, howner_n, hS_target_B]
    have hB_source :
        B.source ((B.edgePieceOrder e)[n + 1]) =
          edgeParam e (intersectionRightParam ((S.cutList e)[n].2)) := by
      rw [B_source_eq_skeleton, howner_n1, hS_source_B]
    exact ⟨c.1, c.2, hB_target, hB_source, hB_targetParam,
      hB_sourceParam, hleft_center, hcenter_right⟩
  have between_gap :
      ∀ (x : {p // p ∈ D.intersectionPoints}) (e : G.edgeFinset)
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          ∃ n, ∃ hn : n + 1 < (B.edgePieceOrder e).length,
            B.target ((B.edgePieceOrder e)[n]) =
                edgeParam e (intersectionLeftParam hx) ∧
              B.source ((B.edgePieceOrder e)[n + 1]) =
                  edgeParam e (intersectionRightParam hx) ∧
                B.targetParam ((B.edgePieceOrder e)[n]) =
                    intersectionLeftParam hx ∧
                  B.sourceParam ((B.edgePieceOrder e)[n + 1]) =
                      intersectionRightParam hx ∧
                    intersectionLeftParam hx < intersectionCenterParam hx ∧
                      intersectionCenterParam hx < intersectionRightParam hx := by
    intro x e hx
    let c : {x : {p // p ∈ D.intersectionPoints} //
        x.1 ∈ D.edgeRelativeInterior e} := ⟨x, hx⟩
    have hmem : c ∈ S.cutList e := S.cutList_mem_all e c
    rcases (List.mem_iff_getElem).mp hmem with ⟨n, hcutn, hget⟩
    have hnS : n + 1 < (S.edgePieceOrder e).length := by
      rw [S.edgePieceOrder_length_eq_retainedIntervals_length e,
        S.retainedIntervals_length_eq_cutList_length e]
      omega
    have hlenS : (S.edgePieceOrder e).length = (B.edgePieceOrder e).length := by
      rw [← B_edgePieceOrder_eq_skeleton e, List.length_map]
    have hnB : n + 1 < (B.edgePieceOrder e).length := by
      simpa [hlenS] using hnS
    have hn0B : n < (B.edgePieceOrder e).length := Nat.lt_of_succ_lt hnB
    have hn1B : n + 1 < (B.edgePieceOrder e).length := hnB
    have hn0S : n < (S.edgePieceOrder e).length := Nat.lt_of_succ_lt hnS
    have hn1S : n + 1 < (S.edgePieceOrder e).length := hnS
    have hmatch := S.edgePieceOrder_matches_retainedIntervals e n hn0S
    have htarget_map : (S.retainedIntervals e)[n]?.map Prod.snd =
        some (S.targetParam ((S.edgePieceOrder e)[n])) := by
      rw [hmatch]
      rfl
    have hsource_match := S.edgePieceOrder_matches_retainedIntervals e (n + 1) hn1S
    have hsource_map : (S.retainedIntervals e)[n + 1]?.map Prod.fst =
        some (S.sourceParam ((S.edgePieceOrder e)[n + 1])) := by
      rw [hsource_match]
      rfl
    have hgap := S.retainedIntervals_cut_gap e n hcutn
    have hS_target :
        S.targetParam ((S.edgePieceOrder e)[n]) =
          intersectionLeftParam ((S.cutList e)[n].2) := by
      rw [hgap.1] at htarget_map
      exact Option.some.inj htarget_map.symm
    have hS_source :
        S.sourceParam ((S.edgePieceOrder e)[n + 1]) =
          intersectionRightParam ((S.cutList e)[n].2) := by
      rw [hgap.2.1] at hsource_map
      exact Option.some.inj hsource_map.symm
    have hleft_center :
        intersectionLeftParam ((S.cutList e)[n].2) <
          intersectionCenterParam ((S.cutList e)[n].2) := hgap.2.2.1
    have hcenter_right :
        intersectionCenterParam ((S.cutList e)[n].2) <
          intersectionRightParam ((S.cutList e)[n].2) := hgap.2.2.2
    have hmap_n :
        pieceEquiv ((B.edgePieceOrder e)[n]) = (S.edgePieceOrder e)[n] := by
      have hgetmap := congrArg (fun l : List S.pieceIndex => l[n]?)
        (B_edgePieceOrder_eq_skeleton e)
      have hgetmap' :
          some (pieceEquiv ((B.edgePieceOrder e)[n])) =
            some ((S.edgePieceOrder e)[n]) := by
        simpa [List.getElem?_map, List.getElem?_eq_getElem, hn0B, hn0S] using hgetmap
      exact Option.some.inj hgetmap'
    have hmap_n1 :
        pieceEquiv ((B.edgePieceOrder e)[n + 1]) =
          (S.edgePieceOrder e)[n + 1] := by
      have hgetmap := congrArg (fun l : List S.pieceIndex => l[n + 1]?)
        (B_edgePieceOrder_eq_skeleton e)
      have hgetmap' :
          some (pieceEquiv ((B.edgePieceOrder e)[n + 1])) =
            some ((S.edgePieceOrder e)[n + 1]) := by
        simpa [List.getElem?_map, List.getElem?_eq_getElem, hn1B, hn1S] using hgetmap
      exact Option.some.inj hgetmap'
    have howner_n :
        S.owner (pieceEquiv ((B.edgePieceOrder e)[n])) = e := by
      have hmem_index : (B.edgePieceOrder e)[n] ∈ B.edgePieceOrder e :=
        List.getElem_mem hn0B
      have hownerB : B.owner ((B.edgePieceOrder e)[n]) = e :=
        (B.edgePieceOrder_owner_iff e ((B.edgePieceOrder e)[n])).1 hmem_index
      rwa [B_owner_eq_skeleton] at hownerB
    have howner_n1 :
        S.owner (pieceEquiv ((B.edgePieceOrder e)[n + 1])) = e := by
      have hmem_index : (B.edgePieceOrder e)[n + 1] ∈ B.edgePieceOrder e :=
        List.getElem_mem hn1B
      have hownerB : B.owner ((B.edgePieceOrder e)[n + 1]) = e :=
        (B.edgePieceOrder_owner_iff e ((B.edgePieceOrder e)[n + 1])).1 hmem_index
      rwa [B_owner_eq_skeleton] at hownerB
    have hS_target_B :
        S.targetParam (pieceEquiv ((B.edgePieceOrder e)[n])) =
          intersectionLeftParam ((S.cutList e)[n].2) := by
      rwa [hmap_n]
    have hS_source_B :
        S.sourceParam (pieceEquiv ((B.edgePieceOrder e)[n + 1])) =
          intersectionRightParam ((S.cutList e)[n].2) := by
      rwa [hmap_n1]
    have htarget :
        B.target ((B.edgePieceOrder e)[n]) =
          edgeParam e (intersectionLeftParam ((S.cutList e)[n].2)) := by
      rw [B_target_eq_skeleton, howner_n, hS_target_B]
    have hsource :
        B.source ((B.edgePieceOrder e)[n + 1]) =
          edgeParam e (intersectionRightParam ((S.cutList e)[n].2)) := by
      rw [B_source_eq_skeleton, howner_n1, hS_source_B]
    have htargetParam :
        B.targetParam ((B.edgePieceOrder e)[n]) =
          intersectionLeftParam ((S.cutList e)[n].2) := by
      rw [B_targetParam_eq_skeleton, hS_target_B]
    have hsourceParam :
        B.sourceParam ((B.edgePieceOrder e)[n + 1]) =
          intersectionRightParam ((S.cutList e)[n].2) := by
      rw [B_sourceParam_eq_skeleton, hS_source_B]
    refine ⟨n, hnB, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [c, hget] using htarget
    · simpa [c, hget] using hsource
    · simpa [c, hget] using htargetParam
    · simpa [c, hget] using hsourceParam
    · simpa [c, hget] using hleft_center
    · simpa [c, hget] using hcenter_right
  have consecutive_parameter_order :
      ∀ e n (hn : n + 1 < (B.edgePieceOrder e).length),
        ∃ x : {p // p ∈ D.intersectionPoints},
          ∃ hx : x.1 ∈ D.edgeRelativeInterior e,
            B.target ((B.edgePieceOrder e)[n]) ∈
                Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              B.source ((B.edgePieceOrder e)[n + 1]) ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                B.targetParam ((B.edgePieceOrder e)[n]) <
                    intersectionCenterParam hx ∧
                  intersectionCenterParam hx <
                    B.sourceParam ((B.edgePieceOrder e)[n + 1]) := by
    intro e n hn
    rcases consecutive_gap e n hn with
      ⟨x, hx, htarget, hsource, htargetParam, hsourceParam,
        hleft_center, hcenter_right⟩
    refine ⟨x, hx, ?_, ?_, ?_, ?_⟩
    · rw [htarget]
      exact (intersection_cut_boundary hx).1
    · rw [hsource]
      exact (intersection_cut_boundary hx).2.2.1
    · rw [htargetParam]
      exact hleft_center
    · rw [hsourceParam]
      exact hcenter_right
  have intersection_between_parameter_order :
      ∀ (x : {p // p ∈ D.intersectionPoints}) (e : G.edgeFinset)
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          ∃ n, ∃ hn : n + 1 < (B.edgePieceOrder e).length,
            B.targetParam ((B.edgePieceOrder e)[n]) <
                intersectionCenterParam hx ∧
              intersectionCenterParam hx <
                B.sourceParam ((B.edgePieceOrder e)[n + 1]) := by
    intro x e hx
    rcases between_gap x e hx with
      ⟨n, hn, _htarget, _hsource, htargetParam, hsourceParam,
        hleft_center, hcenter_right⟩
    refine ⟨n, hn, ?_, ?_⟩
    · rw [htargetParam]
      exact hleft_center
    · rw [hsourceParam]
      exact hcenter_right
  have consecutive_intersection :
      ∀ e n (hn : n + 1 < (B.edgePieceOrder e).length),
        ∃ x : {p // p ∈ D.intersectionPoints},
          x.1 ∈ D.edgeRelativeInterior e ∧
            B.target ((B.edgePieceOrder e)[n]) ∈
                Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              B.target ((B.edgePieceOrder e)[n]) ∈ D.edgeCarrier e ∧
                B.source ((B.edgePieceOrder e)[n + 1]) ∈
                    Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                  B.source ((B.edgePieceOrder e)[n + 1]) ∈ D.edgeCarrier e ∧
                    B.target ((B.edgePieceOrder e)[n]) ≠
                      B.source ((B.edgePieceOrder e)[n + 1]) := by
    intro e n hn
    rcases consecutive_gap e n hn with
      ⟨x, hx, htarget, hsource, _htargetParam, _hsourceParam,
        _hleft_center, _hcenter_right⟩
    refine ⟨x, hx, ?_, ?_, ?_, ?_, ?_⟩
    · rw [htarget]
      exact (intersection_cut_boundary hx).1
    · rw [htarget]
      exact (intersection_cut_boundary hx).2.1
    · rw [hsource]
      exact (intersection_cut_boundary hx).2.2.1
    · rw [hsource]
      exact (intersection_cut_boundary hx).2.2.2.1
    · rw [htarget, hsource]
      exact (intersection_cut_boundary hx).2.2.2.2
  have intersection_between :
      ∀ (x : {p // p ∈ D.intersectionPoints}) (e : G.edgeFinset),
        x.1 ∈ D.edgeRelativeInterior e →
          ∃ n, ∃ hn : n + 1 < (B.edgePieceOrder e).length,
            B.target ((B.edgePieceOrder e)[n]) ∈
                Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              B.target ((B.edgePieceOrder e)[n]) ∈ D.edgeCarrier e ∧
                B.source ((B.edgePieceOrder e)[n + 1]) ∈
                    Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                  B.source ((B.edgePieceOrder e)[n + 1]) ∈ D.edgeCarrier e ∧
                    B.target ((B.edgePieceOrder e)[n]) ≠
                      B.source ((B.edgePieceOrder e)[n + 1]) := by
    intro x e hx
    rcases between_gap x e hx with
      ⟨n, hn, htarget, hsource, _htargetParam, _hsourceParam,
        _hleft_center, _hcenter_right⟩
    refine ⟨n, hn, ?_, ?_, ?_, ?_, ?_⟩
    · rw [htarget]
      exact (intersection_cut_boundary hx).1
    · rw [htarget]
      exact (intersection_cut_boundary hx).2.1
    · rw [hsource]
      exact (intersection_cut_boundary hx).2.2.1
    · rw [hsource]
      exact (intersection_cut_boundary hx).2.2.2.1
    · rw [htarget, hsource]
      exact (intersection_cut_boundary hx).2.2.2.2
  exact ⟨first_source_boundary, last_target_boundary, consecutive_parameter_order,
    intersection_between_parameter_order, consecutive_intersection,
    intersection_between⟩
