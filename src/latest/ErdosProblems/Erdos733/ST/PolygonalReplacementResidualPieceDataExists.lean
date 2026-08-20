import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualPieceData
import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualIntervalPieceVertexAttachment
import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualIntervalPieceIntersectionAttachment
import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualIntervalPiecesPairwiseDisjoint

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementResidualPieceDataExists]
lemma PolygonalReplacementResidualPieceDataExists {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (edgeParam :
      (e : G.edgeFinset) → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (edgeParam_spec :
      ∀ e,
        Continuous (edgeParam e) ∧ Function.Injective (edgeParam e) ∧
          edgeParam e ⟨0, by simp⟩ = D.edgeSource e ∧
            edgeParam e ⟨1, by simp⟩ = D.edgeTarget e ∧
              D.edgeCarrier e = Set.range (edgeParam e) ∧
                D.edgeRelativeInterior e =
                  Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                    edgeParam e
                      ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩))
    (sourceBoundaryParam targetBoundaryParam :
      G.edgeFinset → Set.Icc (0 : ℝ) 1)
    (sourceBoundaryParam_eq :
      ∀ e, edgeParam e (sourceBoundaryParam e) =
        edgeEndpoints.sourceBoundaryPoint e)
    (targetBoundaryParam_eq :
      ∀ e, edgeParam e (targetBoundaryParam e) =
        edgeEndpoints.targetBoundaryPoint e)
    (sourceBoundaryParam_lt_targetBoundaryParam :
      ∀ e, sourceBoundaryParam e < targetBoundaryParam e)
    (intersectionCenterParam :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset},
        x.1 ∈ D.edgeRelativeInterior e → Set.Icc (0 : ℝ) 1)
    (intersectionCenterParam_eq :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          edgeParam e (intersectionCenterParam hx) = x.1)
    (intersectionCenterParam_interior :
      ∀ {x : {p // p ∈ D.intersectionPoints}} {e : G.edgeFinset}
        (hx : x.1 ∈ D.edgeRelativeInterior e),
          0 < (intersectionCenterParam hx).1 ∧
            (intersectionCenterParam hx).1 < 1)
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
    (residualPiece_basic_cert :
      ∃ pieceEquiv : B.pieceIndex ≃ S.pieceIndex,
        (∀ i : B.pieceIndex, B.owner i = S.owner (pieceEquiv i)) ∧
        (∀ i : B.pieceIndex,
          B.sourceParam i = S.sourceParam (pieceEquiv i)) ∧
        (∀ i : B.pieceIndex,
          B.targetParam i = S.targetParam (pieceEquiv i)) ∧
        (∀ i : B.pieceIndex,
          B.source i =
            edgeParam (S.owner (pieceEquiv i))
              (S.sourceParam (pieceEquiv i))) ∧
        (∀ i : B.pieceIndex,
          B.target i =
            edgeParam (S.owner (pieceEquiv i))
              (S.targetParam (pieceEquiv i))) ∧
        (∀ i : B.pieceIndex,
          B.originalPiece i =
            edgeParam (S.owner (pieceEquiv i)) ''
              Set.Icc (S.sourceParam (pieceEquiv i))
                (S.targetParam (pieceEquiv i))) ∧
        (∀ e : G.edgeFinset,
          (B.edgePieceOrder e).map (fun i => pieceEquiv i) =
            S.edgePieceOrder e))
    (originalPiece_avoids_vertex_disk_interiors :
      ∀ i v,
        Disjoint (B.originalPiece i)
          (Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v)))
    (originalPiece_avoids_intersection_disk_interiors :
      ∀ i (x : {p // p ∈ D.intersectionPoints}),
        Disjoint (B.originalPiece i)
          (Metric.ball x.1 (controlDisks.intersectionRadius x)))
    (remaining_arc_covered :
      ∀ ⦃e p⦄,
        p ∈ D.edgeCarrier e →
          (∀ v : V,
            p ∉ Metric.ball (D.vertexPlacement v) (controlDisks.vertexRadius v)) →
            (∀ x : {q // q ∈ D.intersectionPoints},
              p ∉ Metric.ball x.1 (controlDisks.intersectionRadius x)) →
              ∃ i : B.pieceIndex, B.owner i = e ∧ p ∈ B.originalPiece i) :
    Nonempty
      (PolygonalReplacementResidualPieceData G D controlDisks boundaryPoints
        edgeEndpoints) := by
-- BODY
  classical
  rcases residualPiece_basic_cert with
    ⟨pieceEquiv, B_owner_eq_skeleton, B_sourceParam_eq_skeleton,
      B_targetParam_eq_skeleton, B_source_eq_skeleton,
      B_target_eq_skeleton, B_originalPiece_eq_skeleton,
      B_edgePieceOrder_eq_skeleton⟩
  have parameter_bounds :=
    PolygonalReplacementResidualPieceSkeletonParameterBounds G
      sourceBoundaryParam targetBoundaryParam S
  obtain ⟨edgePieceOrder_first_source_boundary,
      edgePieceOrder_last_target_boundary,
      edgePieceOrder_consecutive_intersection_parameter_order,
      edgePieceOrder_intersection_between_parameter_order,
      edgePieceOrder_consecutive_intersection,
      edgePieceOrder_intersection_between⟩ :=
    PolygonalReplacementResidualIntervalPieceBoundaryFields G D controlDisks
      boundaryPoints edgeEndpoints edgeParam sourceBoundaryParam
      targetBoundaryParam sourceBoundaryParam_eq targetBoundaryParam_eq
      intersectionCenterParam intersectionLeftParam intersectionRightParam
      intersection_cut_boundary S B pieceEquiv B_owner_eq_skeleton
      B_sourceParam_eq_skeleton B_targetParam_eq_skeleton
      B_source_eq_skeleton B_target_eq_skeleton
      B_edgePieceOrder_eq_skeleton
  obtain ⟨source_on_control_boundary, target_on_control_boundary⟩ :=
    PolygonalReplacementResidualIntervalPieceEndpointBoundaryAlternatives G D
      controlDisks boundaryPoints edgeEndpoints B
      edgePieceOrder_first_source_boundary edgePieceOrder_last_target_boundary
      edgePieceOrder_consecutive_intersection
  have edgePieceOrder_consecutive_intersection_cut_eq :
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
    have hsource_match :=
      S.edgePieceOrder_matches_retainedIntervals e (n + 1) hn1S
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
  have source_endpoint_order :
      ∀ i : B.pieceIndex,
        (B.sourceParam i = sourceBoundaryParam (B.owner i) ∧
          B.source i = edgeEndpoints.sourceBoundaryPoint (B.owner i) ∧
          B.source i ∈
            Metric.sphere
              (D.vertexPlacement (edgeEndpoints.edgeSourceVertex (B.owner i)))
              (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex (B.owner i))) ∧
          B.source i ∈ D.edgeCarrier (B.owner i)) ∨
          (∃ x : {p // p ∈ D.intersectionPoints},
            ∃ hx : x.1 ∈ D.edgeRelativeInterior (B.owner i),
              B.source i = edgeParam (B.owner i) (intersectionRightParam hx) ∧
                B.sourceParam i = intersectionRightParam hx ∧
                intersectionCenterParam hx < B.sourceParam i ∧
                B.source i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                B.source i ∈ D.edgeCarrier (B.owner i)) := by
    intro i
    let e : G.edgeFinset := B.owner i
    let L : List B.pieceIndex := B.edgePieceOrder e
    have hmem : i ∈ L := by
      dsimp [L, e]
      exact (B.edgePieceOrder_owner_iff (B.owner i) i).2 rfl
    rcases (List.mem_iff_getElem.mp hmem) with ⟨n, hn, hget⟩
    by_cases hn0 : n = 0
    · have hhead : (B.edgePieceOrder e).head? = some i := by
        change L.head? = some i
        subst hn0
        rw [List.head?_eq_getElem?]
        simpa [List.getElem?_eq_getElem hn] using congrArg some hget
      have hfirst := edgePieceOrder_first_source_boundary e i hhead
      have hheadS :
          (S.edgePieceOrder e).head? = some (pieceEquiv i) := by
        rw [← B_edgePieceOrder_eq_skeleton e]
        simp [hhead]
      have hparam : B.sourceParam i = sourceBoundaryParam e := by
        calc
          B.sourceParam i = S.sourceParam (pieceEquiv i) :=
            B_sourceParam_eq_skeleton i
          _ = sourceBoundaryParam e :=
            S.edgePieceOrder_first_sourceParam e (pieceEquiv i) hheadS
      left
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [e] using hparam
      · simpa [e] using hfirst.1
      · simpa [e] using hfirst.2.1
      · simpa [e] using hfirst.2.2
    · rcases Nat.exists_eq_succ_of_ne_zero hn0 with ⟨k, rfl⟩
      have hsucc : k + 1 < (B.edgePieceOrder e).length := by
        change k + 1 < L.length
        simpa [Nat.succ_eq_add_one] using hn
      have hget_succ : (B.edgePieceOrder e)[k + 1] = i := by
        change L[k + 1] = i
        simpa [Nat.succ_eq_add_one] using hget
      rcases edgePieceOrder_consecutive_intersection_cut_eq e k hsucc with
        ⟨x, hx, _htarget, hsource, _htargetParam, hsourceParam,
          _hleft_center, hcenter_right⟩
      right
      change
        ∃ x : {p // p ∈ D.intersectionPoints},
          ∃ hx : x.1 ∈ D.edgeRelativeInterior e,
            B.source i = edgeParam e (intersectionRightParam hx) ∧
              B.sourceParam i = intersectionRightParam hx ∧
              intersectionCenterParam hx < B.sourceParam i ∧
              B.source i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              B.source i ∈ D.edgeCarrier e
      refine ⟨x, hx, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hget_succ] using hsource
      · simpa [hget_succ] using hsourceParam
      · rw [show B.sourceParam i = intersectionRightParam hx by
          simpa [hget_succ] using hsourceParam]
        exact hcenter_right
      · rw [show B.source i = edgeParam e (intersectionRightParam hx) by
          simpa [hget_succ] using hsource]
        exact (intersection_cut_boundary hx).2.2.1
      · rw [show B.source i = edgeParam e (intersectionRightParam hx) by
          simpa [hget_succ] using hsource]
        exact (intersection_cut_boundary hx).2.2.2.1
  have target_endpoint_order :
      ∀ i : B.pieceIndex,
        (B.targetParam i = targetBoundaryParam (B.owner i) ∧
          B.target i = edgeEndpoints.targetBoundaryPoint (B.owner i) ∧
          B.target i ∈
            Metric.sphere
              (D.vertexPlacement (edgeEndpoints.edgeTargetVertex (B.owner i)))
              (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex (B.owner i))) ∧
          B.target i ∈ D.edgeCarrier (B.owner i)) ∨
          (∃ x : {p // p ∈ D.intersectionPoints},
            ∃ hx : x.1 ∈ D.edgeRelativeInterior (B.owner i),
              B.target i = edgeParam (B.owner i) (intersectionLeftParam hx) ∧
                B.targetParam i = intersectionLeftParam hx ∧
                B.targetParam i < intersectionCenterParam hx ∧
                B.target i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                B.target i ∈ D.edgeCarrier (B.owner i)) := by
    intro i
    let e : G.edgeFinset := B.owner i
    let L : List B.pieceIndex := B.edgePieceOrder e
    have hmem : i ∈ L := by
      dsimp [L, e]
      exact (B.edgePieceOrder_owner_iff (B.owner i) i).2 rfl
    rcases (List.mem_iff_getElem.mp hmem) with ⟨n, hn, hget⟩
    by_cases hlast_index : n + 1 = L.length
    · have hlast : (B.edgePieceOrder e).getLast? = some i := by
        change L.getLast? = some i
        rw [List.getLast?_eq_getElem?]
        have hidx : L.length - 1 = n := by omega
        have hlast_lt : L.length - 1 < L.length := by omega
        rw [List.getElem?_eq_getElem hlast_lt]
        simpa [hidx] using congrArg some hget
      have hlast_data := edgePieceOrder_last_target_boundary e i hlast
      have hlastS :
          (S.edgePieceOrder e).getLast? = some (pieceEquiv i) := by
        rw [← B_edgePieceOrder_eq_skeleton e]
        simpa [hlast]
      have hparam : B.targetParam i = targetBoundaryParam e := by
        calc
          B.targetParam i = S.targetParam (pieceEquiv i) :=
            B_targetParam_eq_skeleton i
          _ = targetBoundaryParam e :=
            S.edgePieceOrder_last_targetParam e (pieceEquiv i) hlastS
      left
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [e] using hparam
      · simpa [e] using hlast_data.1
      · simpa [e] using hlast_data.2.1
      · simpa [e] using hlast_data.2.2
    · have hsucc : n + 1 < (B.edgePieceOrder e).length := by
        change n + 1 < L.length
        omega
      have hget_self : (B.edgePieceOrder e)[n] = i := by
        change L[n] = i
        exact hget
      rcases edgePieceOrder_consecutive_intersection_cut_eq e n hsucc with
        ⟨x, hx, htarget, _hsource, htargetParam, _hsourceParam,
          hleft_center, _hcenter_right⟩
      right
      change
        ∃ x : {p // p ∈ D.intersectionPoints},
          ∃ hx : x.1 ∈ D.edgeRelativeInterior e,
            B.target i = edgeParam e (intersectionLeftParam hx) ∧
              B.targetParam i = intersectionLeftParam hx ∧
              B.targetParam i < intersectionCenterParam hx ∧
              B.target i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              B.target i ∈ D.edgeCarrier e
      refine ⟨x, hx, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hget_self] using htarget
      · simpa [hget_self] using htargetParam
      · rw [show B.targetParam i = intersectionLeftParam hx by
          simpa [hget_self] using htargetParam]
        exact hleft_center
      · rw [show B.target i = edgeParam e (intersectionLeftParam hx) by
          simpa [hget_self] using htarget]
        exact (intersection_cut_boundary hx).1
      · rw [show B.target i = edgeParam e (intersectionLeftParam hx) by
          simpa [hget_self] using htarget]
        exact (intersection_cut_boundary hx).2.1
  have vertex_boundary_attached :
      ∀ ⦃v e p⦄,
        v ∈ e.1 →
          p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
            p ∈ D.edgeCarrier e →
              ∃! i : B.pieceIndex, B.owner i = e ∧
                (B.source i = p ∨ B.target i = p) :=
    PolygonalReplacementResidualIntervalPieceVertexAttachment G D controlDisks
      boundaryPoints edgeEndpoints B edgePieceOrder_first_source_boundary
      edgePieceOrder_last_target_boundary edgePieceOrder_consecutive_intersection
  have intersection_boundary_attached :
      ∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e p⦄,
        x.1 ∈ D.edgeRelativeInterior e →
          p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
            p ∈ D.edgeCarrier e →
              ∃! i : B.pieceIndex, B.owner i = e ∧
                (B.source i = p ∨ B.target i = p) :=
    PolygonalReplacementResidualIntervalPieceIntersectionAttachment G D
      controlDisks boundaryPoints edgeEndpoints edgeParam
      sourceBoundaryParam targetBoundaryParam intersectionCenterParam
      intersectionLeftParam intersectionRightParam intersection_cut_boundary
      intersection_cut_boundary_exhaustive S B pieceEquiv
      B_owner_eq_skeleton B_sourceParam_eq_skeleton
      B_targetParam_eq_skeleton B_source_eq_skeleton B_target_eq_skeleton
      B_edgePieceOrder_eq_skeleton edgePieceOrder_first_source_boundary
      edgePieceOrder_last_target_boundary
  have originalPieces_pairwise_disjoint :
      ∀ ⦃i j : B.pieceIndex⦄, i ≠ j →
        Disjoint (B.originalPiece i) (B.originalPiece j) :=
    PolygonalReplacementResidualIntervalPiecesPairwiseDisjoint G D controlDisks
      boundaryPoints edgeEndpoints B originalPiece_avoids_vertex_disk_interiors
      originalPiece_avoids_intersection_disk_interiors
  refine ⟨?data⟩
  exact
    {
        pieceIndex := B.pieceIndex
        pieceIndex_fintype := B.pieceIndex_fintype
        owner := B.owner
        originalPiece := B.originalPiece
        source := B.source
        target := B.target
        edgeParam := edgeParam
        edgeParam_spec := edgeParam_spec
        sourceBoundaryParam := sourceBoundaryParam
        targetBoundaryParam := targetBoundaryParam
        sourceBoundaryParam_eq := sourceBoundaryParam_eq
        targetBoundaryParam_eq := targetBoundaryParam_eq
        sourceBoundaryParam_lt_targetBoundaryParam :=
          sourceBoundaryParam_lt_targetBoundaryParam
        sourceParam := B.sourceParam
        targetParam := B.targetParam
        sourceParam_lt_targetParam := B.sourceParam_lt_targetParam
        source_eq_edgeParam := by
          intro i
          calc
            B.source i =
                edgeParam (S.owner (pieceEquiv i))
                  (S.sourceParam (pieceEquiv i)) :=
              B_source_eq_skeleton i
            _ = edgeParam (B.owner i) (B.sourceParam i) := by
              rw [← B_owner_eq_skeleton i, ← B_sourceParam_eq_skeleton i]
        target_eq_edgeParam := by
          intro i
          calc
            B.target i =
                edgeParam (S.owner (pieceEquiv i))
                  (S.targetParam (pieceEquiv i)) :=
              B_target_eq_skeleton i
            _ = edgeParam (B.owner i) (B.targetParam i) := by
              rw [← B_owner_eq_skeleton i, ← B_targetParam_eq_skeleton i]
        sourceBoundaryParam_le_sourceParam := by
          intro i
          calc
            sourceBoundaryParam (B.owner i) =
                sourceBoundaryParam (S.owner (pieceEquiv i)) := by
              rw [B_owner_eq_skeleton i]
            _ ≤ S.sourceParam (pieceEquiv i) := parameter_bounds.1 (pieceEquiv i)
            _ = B.sourceParam i := by
              rw [← B_sourceParam_eq_skeleton i]
        targetParam_le_targetBoundaryParam := by
          intro i
          calc
            B.targetParam i = S.targetParam (pieceEquiv i) :=
              B_targetParam_eq_skeleton i
            _ ≤ targetBoundaryParam (S.owner (pieceEquiv i)) :=
              parameter_bounds.2 (pieceEquiv i)
            _ = targetBoundaryParam (B.owner i) := by
              rw [← B_owner_eq_skeleton i]
        originalPiece_eq_parameter_interval := by
          intro i
          calc
            B.originalPiece i =
                edgeParam (S.owner (pieceEquiv i)) ''
                  Set.Icc (S.sourceParam (pieceEquiv i))
                    (S.targetParam (pieceEquiv i)) :=
              B_originalPiece_eq_skeleton i
            _ = edgeParam (B.owner i) ''
                Set.Icc (B.sourceParam i) (B.targetParam i) := by
              rw [← B_owner_eq_skeleton i, ← B_sourceParam_eq_skeleton i,
                ← B_targetParam_eq_skeleton i]
        intersectionCenterParam := intersectionCenterParam
        intersectionCenterParam_eq := intersectionCenterParam_eq
        intersectionCenterParam_interior := intersectionCenterParam_interior
        intersectionLeftParam := intersectionLeftParam
        intersectionRightParam := intersectionRightParam
        edgePieceOrder := B.edgePieceOrder
        edgePieceOrder_nonempty := B.edgePieceOrder_nonempty
        edgePieceOrder_nodup := B.edgePieceOrder_nodup
        edgePieceOrder_owner_iff := B.edgePieceOrder_owner_iff
        edgePieceOrder_first_sourceParam := by
          intro e i hhead
          have hheadS :
              (S.edgePieceOrder e).head? = some (pieceEquiv i) := by
            rw [← B_edgePieceOrder_eq_skeleton e]
            simp [hhead]
          calc
            B.sourceParam i = S.sourceParam (pieceEquiv i) :=
              B_sourceParam_eq_skeleton i
            _ = sourceBoundaryParam e :=
              S.edgePieceOrder_first_sourceParam e (pieceEquiv i) hheadS
        edgePieceOrder_last_targetParam := by
          intro e i hlast
          have hlastS :
              (S.edgePieceOrder e).getLast? = some (pieceEquiv i) := by
            rw [← B_edgePieceOrder_eq_skeleton e]
            simp [hlast]
          calc
            B.targetParam i = S.targetParam (pieceEquiv i) :=
              B_targetParam_eq_skeleton i
            _ = targetBoundaryParam e :=
              S.edgePieceOrder_last_targetParam e (pieceEquiv i) hlastS
        edgePieceOrder_consecutive_param_order :=
          B.edgePieceOrder_consecutive_param_order
        edgePieceOrder_consecutive_intersection_cut_eq :=
          edgePieceOrder_consecutive_intersection_cut_eq
        edgePieceOrder_consecutive_intersection_parameter_order :=
          edgePieceOrder_consecutive_intersection_parameter_order
        edgePieceOrder_intersection_between_parameter_order :=
          edgePieceOrder_intersection_between_parameter_order
        edgePieceOrder_first_source_boundary :=
          edgePieceOrder_first_source_boundary
        edgePieceOrder_last_target_boundary :=
          edgePieceOrder_last_target_boundary
        edgePieceOrder_consecutive_intersection :=
          edgePieceOrder_consecutive_intersection
        edgePieceOrder_intersection_between :=
          edgePieceOrder_intersection_between
        originalPiece_compact := B.originalPiece_compact
        originalPiece_subset_owner := B.originalPiece_subset_owner
        source_mem_originalPiece := B.source_mem_originalPiece
        target_mem_originalPiece := B.target_mem_originalPiece
        source_ne_target := B.source_ne_target
        source_on_control_boundary := source_on_control_boundary
        target_on_control_boundary := target_on_control_boundary
        source_endpoint_order := source_endpoint_order
        target_endpoint_order := target_endpoint_order
        remaining_arc_covered := remaining_arc_covered
        vertex_boundary_attached := vertex_boundary_attached
        intersection_boundary_attached := intersection_boundary_attached
        originalPiece_avoids_vertex_disk_interiors :=
          originalPiece_avoids_vertex_disk_interiors
        originalPiece_avoids_intersection_disk_interiors :=
          originalPiece_avoids_intersection_disk_interiors
        originalPieces_pairwise_disjoint := originalPieces_pairwise_disjoint }
