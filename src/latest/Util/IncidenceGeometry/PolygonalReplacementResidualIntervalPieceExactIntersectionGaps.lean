import Util.IncidenceGeometry.PolygonalReplacementResidualIntervalPieceBoundaryFields

open Classical
noncomputable section

universe u


lemma PolygonalReplacementResidualIntervalPieceExactIntersectionGaps {V : Type u}
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
    (∀ e n (hn : n + 1 < (B.edgePieceOrder e).length),
      ∃ c : {x : {p // p ∈ D.intersectionPoints} //
          x.1 ∈ D.edgeRelativeInterior e},
        (S.cutList e)[n]? = some c ∧
          B.target ((B.edgePieceOrder e)[n]) =
              edgeParam e (intersectionLeftParam c.2) ∧
            B.source ((B.edgePieceOrder e)[n + 1]) =
                edgeParam e (intersectionRightParam c.2) ∧
              B.targetParam ((B.edgePieceOrder e)[n]) =
                  intersectionLeftParam c.2 ∧
                B.sourceParam ((B.edgePieceOrder e)[n + 1]) =
                    intersectionRightParam c.2 ∧
                  intersectionLeftParam c.2 < intersectionCenterParam c.2 ∧
                    intersectionCenterParam c.2 < intersectionRightParam c.2) ∧
      (∀ (x : {p // p ∈ D.intersectionPoints}) (e : G.edgeFinset)
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          ∃ n, ∃ hn : n + 1 < (B.edgePieceOrder e).length,
            (S.cutList e)[n]? = some (⟨x, hx⟩ :
              {x : {p // p ∈ D.intersectionPoints} //
                x.1 ∈ D.edgeRelativeInterior e}) ∧
              B.target ((B.edgePieceOrder e)[n]) =
                  edgeParam e (intersectionLeftParam hx) ∧
                B.source ((B.edgePieceOrder e)[n + 1]) =
                    edgeParam e (intersectionRightParam hx) ∧
                  B.targetParam ((B.edgePieceOrder e)[n]) =
                      intersectionLeftParam hx ∧
                    B.sourceParam ((B.edgePieceOrder e)[n + 1]) =
                        intersectionRightParam hx ∧
                      intersectionLeftParam hx < intersectionCenterParam hx ∧
                        intersectionCenterParam hx < intersectionRightParam hx) := by
  classical
  have consecutive_gap :
      ∀ e n (hn : n + 1 < (B.edgePieceOrder e).length),
        ∃ c : {x : {p // p ∈ D.intersectionPoints} //
            x.1 ∈ D.edgeRelativeInterior e},
          (S.cutList e)[n]? = some c ∧
            B.target ((B.edgePieceOrder e)[n]) =
                edgeParam e (intersectionLeftParam c.2) ∧
              B.source ((B.edgePieceOrder e)[n + 1]) =
                  edgeParam e (intersectionRightParam c.2) ∧
                B.targetParam ((B.edgePieceOrder e)[n]) =
                    intersectionLeftParam c.2 ∧
                  B.sourceParam ((B.edgePieceOrder e)[n + 1]) =
                      intersectionRightParam c.2 ∧
                    intersectionLeftParam c.2 < intersectionCenterParam c.2 ∧
                      intersectionCenterParam c.2 < intersectionRightParam c.2 := by
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
    have hcget : (S.cutList e)[n]? = some c := by
      rw [List.getElem?_eq_getElem hcutn]
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
    exact ⟨c, hcget, hB_target, hB_source, hB_targetParam,
      hB_sourceParam, hleft_center, hcenter_right⟩
  have between_gap :
      ∀ (x : {p // p ∈ D.intersectionPoints}) (e : G.edgeFinset)
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          ∃ n, ∃ hn : n + 1 < (B.edgePieceOrder e).length,
            (S.cutList e)[n]? = some (⟨x, hx⟩ :
              {x : {p // p ∈ D.intersectionPoints} //
                x.1 ∈ D.edgeRelativeInterior e}) ∧
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
    have hcget : (S.cutList e)[n]? = some c := by
      rw [List.getElem?_eq_getElem hcutn]
      simp [hget]
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
    refine ⟨n, hnB, hcget, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [c, hget] using htarget
    · simpa [c, hget] using hsource
    · simpa [c, hget] using htargetParam
    · simpa [c, hget] using hsourceParam
    · simpa [c, hget] using hleft_center
    · simpa [c, hget] using hcenter_right
  exact ⟨consecutive_gap, between_gap⟩
