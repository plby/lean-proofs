import ErdosProblems.Erdos733.ST.PolygonalReplacementResidualIntervalPieceEndpointBoundaryAlternatives

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementResidualIntervalPieceVertexAttachment]
lemma PolygonalReplacementResidualIntervalPieceVertexAttachment {V : Type u}
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
    ∀ ⦃v e p⦄,
      v ∈ e.1 →
        p ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
          p ∈ D.edgeCarrier e →
            ∃! i : B.pieceIndex, B.owner i = e ∧
              (B.source i = p ∨ B.target i = p) := by
-- BODY
  classical
  have edgeSource_ne_target :
      ∀ e : G.edgeFinset, D.edgeSource e ≠ D.edgeTarget e := by
    intro e
    rcases D.edge_is_simple_lineSegment_or_circularArc e with hline | harc
    · exact hline.1
    · rcases harc with
        ⟨_c, _r, γ, _hr, _hcont, hinj, _hdist, hzero, hone,
          _hcarrier, _hrelativeInterior⟩
      intro hst
      have h01 :
          (⟨(0 : ℝ), by simp⟩ : Set.Icc (0 : ℝ) 1) =
            ⟨(1 : ℝ), by simp⟩ := by
        apply hinj
        rw [hzero, hone]
        exact hst
      have hval := congrArg Subtype.val h01
      norm_num at hval
  have endpoint_vertices_ne :
      ∀ e : G.edgeFinset,
        edgeEndpoints.edgeSourceVertex e ≠ edgeEndpoints.edgeTargetVertex e := by
    intro e hvertices
    exact edgeSource_ne_target e (by
      rw [edgeEndpoints.edgeSource_eq_vertexPlacement e,
        edgeEndpoints.edgeTarget_eq_vertexPlacement e, hvertices])
  have incident_endpoint :
      ∀ (e : G.edgeFinset) (v : V), v ∈ e.1 →
        v = edgeEndpoints.edgeSourceVertex e ∨
          v = edgeEndpoints.edgeTargetVertex e := by
    intro e v hv
    rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, heq, hends⟩
    have hv_ab : v ∈ (Sym2.mk a b : Sym2 V) := by
      simpa [heq] using hv
    have hv_cases : v = a ∨ v = b := by
      simpa [Sym2.mem_iff'] using hv_ab
    rcases hends with hends | hends
    · rcases hends with ⟨hsource, htarget⟩
      have hsource_vertex_eq : edgeEndpoints.edgeSourceVertex e = a := by
        apply D.vertexPlacement_injective
        calc
          D.vertexPlacement (edgeEndpoints.edgeSourceVertex e) = D.edgeSource e :=
            (edgeEndpoints.edgeSource_eq_vertexPlacement e).symm
          _ = D.vertexPlacement a := hsource
      have htarget_vertex_eq : edgeEndpoints.edgeTargetVertex e = b := by
        apply D.vertexPlacement_injective
        calc
          D.vertexPlacement (edgeEndpoints.edgeTargetVertex e) = D.edgeTarget e :=
            (edgeEndpoints.edgeTarget_eq_vertexPlacement e).symm
          _ = D.vertexPlacement b := htarget
      rcases hv_cases with rfl | rfl
      · exact Or.inl hsource_vertex_eq.symm
      · exact Or.inr htarget_vertex_eq.symm
    · rcases hends with ⟨hsource, htarget⟩
      have hsource_vertex_eq : edgeEndpoints.edgeSourceVertex e = b := by
        apply D.vertexPlacement_injective
        calc
          D.vertexPlacement (edgeEndpoints.edgeSourceVertex e) = D.edgeSource e :=
            (edgeEndpoints.edgeSource_eq_vertexPlacement e).symm
          _ = D.vertexPlacement b := hsource
      have htarget_vertex_eq : edgeEndpoints.edgeTargetVertex e = a := by
        apply D.vertexPlacement_injective
        calc
          D.vertexPlacement (edgeEndpoints.edgeTargetVertex e) = D.edgeTarget e :=
            (edgeEndpoints.edgeTarget_eq_vertexPlacement e).symm
          _ = D.vertexPlacement a := htarget
      rcases hv_cases with rfl | rfl
      · exact Or.inr htarget_vertex_eq.symm
      · exact Or.inl hsource_vertex_eq.symm
  have vertex_intersection_contradiction :
      ∀ (v : V) (x : {p // p ∈ D.intersectionPoints})
        {q : EuclideanSpace ℝ (Fin 2)},
        q ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
          q ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) → False := by
    intro v x q hv hx
    have hdis := controlDisks.vertex_intersection_disjoint v x
    exact (Set.disjoint_left.mp hdis)
      (Metric.sphere_subset_closedBall hv) (Metric.sphere_subset_closedBall hx)
  have vertex_vertex_contradiction :
      ∀ {v w : V} {q : EuclideanSpace ℝ (Fin 2)},
        v ≠ w →
          q ∈ Metric.sphere (D.vertexPlacement v) (controlDisks.vertexRadius v) →
            q ∈ Metric.sphere (D.vertexPlacement w) (controlDisks.vertexRadius w) →
              False := by
    intro v w q hvw hv hw
    have hdis := controlDisks.vertex_vertex_disjoint hvw
    exact (Set.disjoint_left.mp hdis)
      (Metric.sphere_subset_closedBall hv) (Metric.sphere_subset_closedBall hw)
  have head_exists :
      ∀ e : G.edgeFinset, ∃ i : B.pieceIndex,
        (B.edgePieceOrder e).head? = some i := by
    intro e
    have hpos : 0 < (B.edgePieceOrder e).length := by
      have hne := B.edgePieceOrder_nonempty e
      omega
    refine ⟨(B.edgePieceOrder e)[0], ?_⟩
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_eq_getElem hpos]
  have last_exists :
      ∀ e : G.edgeFinset, ∃ i : B.pieceIndex,
        (B.edgePieceOrder e).getLast? = some i := by
    intro e
    have hpos : 0 < (B.edgePieceOrder e).length := by
      have hne := B.edgePieceOrder_nonempty e
      omega
    have hlast_lt : (B.edgePieceOrder e).length - 1 <
        (B.edgePieceOrder e).length := by
      omega
    refine ⟨(B.edgePieceOrder e)[(B.edgePieceOrder e).length - 1], ?_⟩
    rw [List.getLast?_eq_getElem?]
    rw [List.getElem?_eq_getElem hlast_lt]
  have source_boundary_head :
      ∀ {e : G.edgeFinset} {j : B.pieceIndex},
        B.owner j = e →
          (B.source j = edgeEndpoints.sourceBoundaryPoint e ∨
            B.target j = edgeEndpoints.sourceBoundaryPoint e) →
            (B.edgePieceOrder e).head? = some j := by
    intro e j howner hj
    let L : List B.pieceIndex := B.edgePieceOrder e
    have hmem : j ∈ L := by
      dsimp [L]
      exact (B.edgePieceOrder_owner_iff e j).2 howner
    rcases (List.mem_iff_getElem.mp hmem) with ⟨n, hn, hget⟩
    rcases hj with hsource | htarget
    · by_cases hn0 : n = 0
      · subst hn0
        change L.head? = some j
        rw [List.head?_eq_getElem?]
        simpa [List.getElem?_eq_getElem hn] using congrArg some hget
      · exfalso
        rcases Nat.exists_eq_succ_of_ne_zero hn0 with ⟨k, rfl⟩
        have hsucc : k + 1 < (B.edgePieceOrder e).length := by
          change k + 1 < L.length
          simpa [Nat.succ_eq_add_one] using hn
        have hget_succ : (B.edgePieceOrder e)[k + 1] = j := by
          change L[k + 1] = j
          simpa [Nat.succ_eq_add_one] using hget
        rcases consecutive_intersection e k hsucc with
          ⟨x, _hx, _htarget_sphere, _htarget_carrier, hsource_sphere,
            _hsource_carrier, _hne⟩
        have hvertex :
            B.source j ∈
              Metric.sphere
                (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
                (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) := by
          rw [hsource]
          exact (edgeEndpoints.sourceBoundary_on_control_boundary e).1
        have hintersection :
            B.source j ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
          simpa [hget_succ] using hsource_sphere
        exact vertex_intersection_contradiction
          (edgeEndpoints.edgeSourceVertex e) x hvertex hintersection
    · by_cases hlast_index : n + 1 = L.length
      · exfalso
        have hlast : (B.edgePieceOrder e).getLast? = some j := by
          change L.getLast? = some j
          rw [List.getLast?_eq_getElem?]
          have hidx : L.length - 1 = n := by omega
          have hlast_lt : L.length - 1 < L.length := by omega
          rw [List.getElem?_eq_getElem hlast_lt]
          simpa [hidx] using congrArg some hget
        have hlast_data := last_target_boundary e j hlast
        have hsource_vertex :
            B.target j ∈
              Metric.sphere
                (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
                (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) := by
          rw [htarget]
          exact (edgeEndpoints.sourceBoundary_on_control_boundary e).1
        have htarget_vertex :
            B.target j ∈
              Metric.sphere
                (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
                (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) :=
          hlast_data.2.1
        exact vertex_vertex_contradiction (endpoint_vertices_ne e)
          hsource_vertex htarget_vertex
      · exfalso
        have hsucc : n + 1 < (B.edgePieceOrder e).length := by
          change n + 1 < L.length
          omega
        have hget_self : (B.edgePieceOrder e)[n] = j := by
          change L[n] = j
          exact hget
        rcases consecutive_intersection e n hsucc with
          ⟨x, _hx, htarget_sphere, _htarget_carrier, _hsource_sphere,
            _hsource_carrier, _hne⟩
        have hvertex :
            B.target j ∈
              Metric.sphere
                (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
                (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) := by
          rw [htarget]
          exact (edgeEndpoints.sourceBoundary_on_control_boundary e).1
        have hintersection :
            B.target j ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
          simpa [hget_self] using htarget_sphere
        exact vertex_intersection_contradiction
          (edgeEndpoints.edgeSourceVertex e) x hvertex hintersection
  have target_boundary_last :
      ∀ {e : G.edgeFinset} {j : B.pieceIndex},
        B.owner j = e →
          (B.source j = edgeEndpoints.targetBoundaryPoint e ∨
            B.target j = edgeEndpoints.targetBoundaryPoint e) →
            (B.edgePieceOrder e).getLast? = some j := by
    intro e j howner hj
    let L : List B.pieceIndex := B.edgePieceOrder e
    have hmem : j ∈ L := by
      dsimp [L]
      exact (B.edgePieceOrder_owner_iff e j).2 howner
    rcases (List.mem_iff_getElem.mp hmem) with ⟨n, hn, hget⟩
    rcases hj with hsource | htarget
    · by_cases hn0 : n = 0
      · exfalso
        have hhead : (B.edgePieceOrder e).head? = some j := by
          change L.head? = some j
          subst hn0
          rw [List.head?_eq_getElem?]
          simpa [List.getElem?_eq_getElem hn] using congrArg some hget
        have hhead_data := first_source_boundary e j hhead
        have htarget_vertex :
            B.source j ∈
              Metric.sphere
                (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
                (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) := by
          rw [hsource]
          exact (edgeEndpoints.targetBoundary_on_control_boundary e).1
        have hsource_vertex :
            B.source j ∈
              Metric.sphere
                (D.vertexPlacement (edgeEndpoints.edgeSourceVertex e))
                (controlDisks.vertexRadius (edgeEndpoints.edgeSourceVertex e)) :=
          hhead_data.2.1
        exact vertex_vertex_contradiction (endpoint_vertices_ne e).symm
          htarget_vertex hsource_vertex
      · exfalso
        rcases Nat.exists_eq_succ_of_ne_zero hn0 with ⟨k, rfl⟩
        have hsucc : k + 1 < (B.edgePieceOrder e).length := by
          change k + 1 < L.length
          simpa [Nat.succ_eq_add_one] using hn
        have hget_succ : (B.edgePieceOrder e)[k + 1] = j := by
          change L[k + 1] = j
          simpa [Nat.succ_eq_add_one] using hget
        rcases consecutive_intersection e k hsucc with
          ⟨x, _hx, _htarget_sphere, _htarget_carrier, hsource_sphere,
            _hsource_carrier, _hne⟩
        have hvertex :
            B.source j ∈
              Metric.sphere
                (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
                (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) := by
          rw [hsource]
          exact (edgeEndpoints.targetBoundary_on_control_boundary e).1
        have hintersection :
            B.source j ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
          simpa [hget_succ] using hsource_sphere
        exact vertex_intersection_contradiction
          (edgeEndpoints.edgeTargetVertex e) x hvertex hintersection
    · by_cases hlast_index : n + 1 = L.length
      · have hlast : (B.edgePieceOrder e).getLast? = some j := by
          change L.getLast? = some j
          rw [List.getLast?_eq_getElem?]
          have hidx : L.length - 1 = n := by omega
          have hlast_lt : L.length - 1 < L.length := by omega
          rw [List.getElem?_eq_getElem hlast_lt]
          simpa [hidx] using congrArg some hget
        exact hlast
      · exfalso
        have hsucc : n + 1 < (B.edgePieceOrder e).length := by
          change n + 1 < L.length
          omega
        have hget_self : (B.edgePieceOrder e)[n] = j := by
          change L[n] = j
          exact hget
        rcases consecutive_intersection e n hsucc with
          ⟨x, _hx, htarget_sphere, _htarget_carrier, _hsource_sphere,
            _hsource_carrier, _hne⟩
        have hvertex :
            B.target j ∈
              Metric.sphere
                (D.vertexPlacement (edgeEndpoints.edgeTargetVertex e))
                (controlDisks.vertexRadius (edgeEndpoints.edgeTargetVertex e)) := by
          rw [htarget]
          exact (edgeEndpoints.targetBoundary_on_control_boundary e).1
        have hintersection :
            B.target j ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) := by
          simpa [hget_self] using htarget_sphere
        exact vertex_intersection_contradiction
          (edgeEndpoints.edgeTargetVertex e) x hvertex hintersection
  intro v e p hv hpSphere hpCarrier
  rcases incident_endpoint e v hv with hv_source | hv_target
  · subst hv_source
    have hp_eq_source :
        p = edgeEndpoints.sourceBoundaryPoint e :=
      edgeEndpoints.sourceBoundary_unique e p hpSphere hpCarrier
    rcases head_exists e with ⟨i, hhead⟩
    refine ⟨i, ?_, ?_⟩
    · have hmemOpt : i ∈ (B.edgePieceOrder e).head? := by
        simp [hhead]
      have hmem : i ∈ B.edgePieceOrder e := List.mem_of_mem_head? hmemOpt
      have howner : B.owner i = e := (B.edgePieceOrder_owner_iff e i).1 hmem
      have hfirst := first_source_boundary e i hhead
      refine ⟨howner, Or.inl ?_⟩
      exact hfirst.1.trans hp_eq_source.symm
    · intro j hj
      rcases hj with ⟨howner, hendpoint⟩
      have hjhead : (B.edgePieceOrder e).head? = some j :=
        source_boundary_head howner (by
          rcases hendpoint with hsource | htarget
          · exact Or.inl (hsource.trans hp_eq_source)
          · exact Or.inr (htarget.trans hp_eq_source))
      rw [hhead] at hjhead
      exact (Option.some.inj hjhead).symm
  · subst hv_target
    have hp_eq_target :
        p = edgeEndpoints.targetBoundaryPoint e :=
      edgeEndpoints.targetBoundary_unique e p hpSphere hpCarrier
    rcases last_exists e with ⟨i, hlast⟩
    refine ⟨i, ?_, ?_⟩
    · have hmemOpt : i ∈ (B.edgePieceOrder e).getLast? := by
        simp [hlast]
      have hmem : i ∈ B.edgePieceOrder e := List.mem_of_mem_getLast? hmemOpt
      have howner : B.owner i = e := (B.edgePieceOrder_owner_iff e i).1 hmem
      have hlast_data := last_target_boundary e i hlast
      refine ⟨howner, Or.inr ?_⟩
      exact hlast_data.1.trans hp_eq_target.symm
    · intro j hj
      rcases hj with ⟨howner, hendpoint⟩
      have hjlast : (B.edgePieceOrder e).getLast? = some j :=
        target_boundary_last howner (by
          rcases hendpoint with hsource | htarget
          · exact Or.inl (hsource.trans hp_eq_target)
          · exact Or.inr (htarget.trans hp_eq_target))
      rw [hlast] at hjlast
      exact (Option.some.inj hjlast).symm
