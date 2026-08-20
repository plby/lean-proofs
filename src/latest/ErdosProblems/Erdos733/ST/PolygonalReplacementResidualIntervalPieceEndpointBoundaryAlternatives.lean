import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualIntervalPieceBasicData

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementResidualIntervalPieceEndpointBoundaryAlternatives]
lemma PolygonalReplacementResidualIntervalPieceEndpointBoundaryAlternatives {V : Type u}
    [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints : PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks)
    (edgeEndpoints :
      PolygonalReplacementEdgeBoundaryEndpointData G D controlDisks boundaryPoints)
    (B : PolygonalReplacementResidualIntervalPieceBasicData G D controlDisks
        boundaryPoints edgeEndpoints)
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
              B.target i ∈ D.edgeCarrier e)
    (consecutive_intersection :
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
                      B.source ((B.edgePieceOrder e)[n + 1])) :
    (∀ i : B.pieceIndex,
      (∃ v : V,
        v ∈ (B.owner i).1 ∧
          B.source i ∈
            Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
            B.source i ∈ D.edgeCarrier (B.owner i)) ∨
        (∃ x : {p // p ∈ D.intersectionPoints},
          x.1 ∈ D.edgeRelativeInterior (B.owner i) ∧
            B.source i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
              B.source i ∈ D.edgeCarrier (B.owner i))) ∧
      (∀ i : B.pieceIndex,
        (∃ v : V,
          v ∈ (B.owner i).1 ∧
            B.target i ∈
              Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
              B.target i ∈ D.edgeCarrier (B.owner i)) ∨
          (∃ x : {p // p ∈ D.intersectionPoints},
            x.1 ∈ D.edgeRelativeInterior (B.owner i) ∧
              B.target i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                B.target i ∈ D.edgeCarrier (B.owner i))) := by
-- BODY
  classical
  have source_on_control_boundary :
      ∀ i : B.pieceIndex,
        (∃ v : V,
          v ∈ (B.owner i).1 ∧
            B.source i ∈
              Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
              B.source i ∈ D.edgeCarrier (B.owner i)) ∨
          (∃ x : {p // p ∈ D.intersectionPoints},
            x.1 ∈ D.edgeRelativeInterior (B.owner i) ∧
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
      have hfirst := first_source_boundary e i hhead
      left
      refine ⟨edgeEndpoints.edgeSourceVertex e, ?_, ?_, ?_⟩
      · change edgeEndpoints.edgeSourceVertex e ∈ e.1
        exact edgeEndpoints.edgeSourceVertex_mem e
      · change B.source i ∈
          Metric.sphere (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
            (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e))
        exact hfirst.2.1
      · change B.source i ∈ D.edgeCarrier e
        exact hfirst.2.2
    · rcases Nat.exists_eq_succ_of_ne_zero hn0 with ⟨k, rfl⟩
      have hsucc : k + 1 < (B.edgePieceOrder e).length := by
        change k + 1 < L.length
        simpa [Nat.succ_eq_add_one] using hn
      have hget_succ : (B.edgePieceOrder e)[k + 1] = i := by
        change L[k + 1] = i
        simpa [Nat.succ_eq_add_one] using hget
      rcases consecutive_intersection e k hsucc with
        ⟨x, hx, _htarget_sphere, _htarget_carrier, hsource_sphere,
          hsource_carrier, _hne⟩
      right
      refine ⟨x, ?_, ?_, ?_⟩
      · change x.1 ∈ D.edgeRelativeInterior e
        exact hx
      · change B.source i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x)
        simpa [hget_succ] using hsource_sphere
      · change B.source i ∈ D.edgeCarrier e
        simpa [hget_succ] using hsource_carrier
  have target_on_control_boundary :
      ∀ i : B.pieceIndex,
        (∃ v : V,
          v ∈ (B.owner i).1 ∧
            B.target i ∈
              Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) ∧
              B.target i ∈ D.edgeCarrier (B.owner i)) ∨
          (∃ x : {p // p ∈ D.intersectionPoints},
            x.1 ∈ D.edgeRelativeInterior (B.owner i) ∧
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
      have hlast_data := last_target_boundary e i hlast
      left
      refine ⟨edgeEndpoints.edgeTargetVertex e, ?_, ?_, ?_⟩
      · change edgeEndpoints.edgeTargetVertex e ∈ e.1
        exact edgeEndpoints.edgeTargetVertex_mem e
      · change B.target i ∈
          Metric.sphere (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
            (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e))
        exact hlast_data.2.1
      · change B.target i ∈ D.edgeCarrier e
        exact hlast_data.2.2
    · have hsucc : n + 1 < (B.edgePieceOrder e).length := by
        change n + 1 < L.length
        omega
      have hget_self : (B.edgePieceOrder e)[n] = i := by
        change L[n] = i
        exact hget
      rcases consecutive_intersection e n hsucc with
        ⟨x, hx, htarget_sphere, htarget_carrier, _hsource_sphere,
          _hsource_carrier, _hne⟩
      right
      refine ⟨x, ?_, ?_, ?_⟩
      · change x.1 ∈ D.edgeRelativeInterior e
        exact hx
      · change B.target i ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x)
        simpa [hget_self] using htarget_sphere
      · change B.target i ∈ D.edgeCarrier e
        simpa [hget_self] using htarget_carrier
  exact ⟨source_on_control_boundary, target_on_control_boundary⟩
