import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.CrossingFreeEdgeInteriorDisjoint
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImageWithoutEdge
import ErdosProblems.Erdos733.ST.OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalArcCarrierCompact
import ErdosProblems.Erdos733.ST.PolygonalArcSourceEndpointRayCover
import ErdosProblems.Erdos733.ST.PolygonalArcTargetEndpointRayCover

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingEndpointLocalGermCover]
lemma PlaneDrawingEndpointLocalGermCover {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (e : G.edgeFinset) (γ : PolygonalArc) :
    D.edgeArc e = γ →
      let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
      let d₀ : EuclideanSpace ℝ (Fin 2) := γ.vertices[1]'hfirst - γ.source
      let hprev : γ.vertices.length - 2 < γ.vertices.length := by
        have hlen := γ.length_ge_two
        omega
      let d₁ : EuclideanSpace ℝ (Fin 2) :=
        γ.vertices[γ.vertices.length - 2]'hprev - γ.target
      ∃ r₀ r₁ : ℝ, 0 < r₀ ∧ 0 < r₁ ∧
        ∃ initialDirections terminalDirections : Finset (EuclideanSpace ℝ (Fin 2)),
          (∀ v ∈ initialDirections, ¬ ∃ a : ℝ, 0 < a ∧ v = a • d₀) ∧
            (∀ v ∈ terminalDirections, ¬ ∃ a : ℝ, 0 < a ∧ v = a • d₁) ∧
              (Metric.ball γ.source r₀ ∩ OrdinaryDrawingImageWithoutEdge G D e ⊆
                ({γ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∪
                  ⋃ v : {v : EuclideanSpace ℝ (Fin 2) // v ∈ initialDirections},
                    {x | ∃ c : ℝ, 0 ≤ c ∧ x = γ.source + c • v.1}) ∧
                (Metric.ball γ.target r₁ ∩ OrdinaryDrawingImageWithoutEdge G D e ⊆
                  ({γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
                    ⋃ v : {v : EuclideanSpace ℝ (Fin 2) // v ∈ terminalDirections},
                      {x | ∃ c : ℝ, 0 ≤ c ∧ x = γ.target + c • v.1}) := by
-- BODY
  intro hγ
  classical
  dsimp
  have hsource_vertex : ∃ u : V, γ.source = D.vertexPlacement u := by
    rcases D.edgeArc_endpoints e with ⟨u, v, _hadj, _hedge, hend | hend⟩
    · refine ⟨u, ?_⟩
      have hsrc : (D.edgeArc e).source = γ.source := by rw [hγ]
      exact hsrc.symm.trans hend.1
    · refine ⟨v, ?_⟩
      have hsrc : (D.edgeArc e).source = γ.source := by rw [hγ]
      exact hsrc.symm.trans hend.1
  have htarget_vertex : ∃ u : V, γ.target = D.vertexPlacement u := by
    rcases D.edgeArc_endpoints e with ⟨u, v, _hadj, _hedge, hend | hend⟩
    · refine ⟨v, ?_⟩
      have htgt : (D.edgeArc e).target = γ.target := by rw [hγ]
      exact htgt.symm.trans hend.2
    · refine ⟨u, ?_⟩
      have htgt : (D.edgeArc e).target = γ.target := by rw [hγ]
      exact htgt.symm.trans hend.2
  have source_mem_carrier :
      ∀ δ : PolygonalArc, δ.source ∈ δ.carrier := by
    intro δ
    rw [δ.carrier_eq]
    have h0 : 0 < δ.vertices.length := by
      have hlen := δ.length_ge_two
      omega
    have hfirst : 0 + 1 < δ.vertices.length := by
      have hlen := δ.length_ge_two
      omega
    have hsource0 : δ.vertices[0] = δ.source := by
      have hget : δ.vertices[0]? = some δ.vertices[0] :=
        List.getElem?_eq_getElem h0
      rw [← List.head?_eq_getElem?, δ.source_eq_head] at hget
      exact Option.some.inj hget.symm
    refine ⟨0, hfirst, ?_⟩
    simpa [hsource0] using
      (left_mem_segment ℝ δ.vertices[0] δ.vertices[0 + 1])
  have endpointCover :
      ∀ (x d : EuclideanSpace ℝ (Fin 2)), d ≠ 0 →
        (∃ u : V, x = D.vertexPlacement u) →
        ∀ (iSel : ℕ)
          (hiSel : iSel + 1 < (D.edgeArc e).vertices.length),
          segment ℝ x (x + d) =
              segment ℝ (D.edgeArc e).vertices[iSel]
                (D.edgeArc e).vertices[iSel + 1] →
          ∃ r : ℝ, 0 < r ∧
            ∃ directions : Finset (EuclideanSpace ℝ (Fin 2)),
              (∀ v ∈ directions, ¬ ∃ a : ℝ, 0 < a ∧ v = a • d) ∧
                (Metric.ball x r ∩ OrdinaryDrawingImageWithoutEdge G D e ⊆
                  ({x} : Set (EuclideanSpace ℝ (Fin 2))) ∪
                    ⋃ v : {v : EuclideanSpace ℝ (Fin 2) // v ∈ directions},
                      {y | ∃ c : ℝ, 0 ≤ c ∧ y = x + c • v.1}) := by
    intro x d hd hx_vertex iSel hiSel hsegSel
    let sourceRayRadius : G.edgeFinset → ℝ := fun f =>
      Classical.choose (PolygonalArcSourceEndpointRayCover (D.edgeArc f))
    have sourceRayRadius_pos :
        ∀ f : G.edgeFinset, 0 < sourceRayRadius f := by
      intro f
      dsimp [sourceRayRadius]
      exact (Classical.choose_spec
        (PolygonalArcSourceEndpointRayCover (D.edgeArc f))).1
    have sourceRayRadius_spec :
        ∀ f : G.edgeFinset,
          let δ := D.edgeArc f
          let hfirst : 1 < δ.vertices.length :=
            Nat.lt_of_succ_le δ.length_ge_two
          Metric.ball δ.source (sourceRayRadius f) ∩ δ.carrier ⊆
            {y | ∃ c : ℝ, 0 ≤ c ∧
              y = δ.source + c • (δ.vertices[1]'hfirst - δ.source)} := by
      intro f
      dsimp [sourceRayRadius]
      exact (Classical.choose_spec
        (PolygonalArcSourceEndpointRayCover (D.edgeArc f))).2
    let targetRayRadius : G.edgeFinset → ℝ := fun f =>
      Classical.choose (PolygonalArcTargetEndpointRayCover (D.edgeArc f))
    have targetRayRadius_pos :
        ∀ f : G.edgeFinset, 0 < targetRayRadius f := by
      intro f
      dsimp [targetRayRadius]
      exact (Classical.choose_spec
        (PolygonalArcTargetEndpointRayCover (D.edgeArc f))).1
    have targetRayRadius_spec :
        ∀ f : G.edgeFinset,
          let δ := D.edgeArc f
          let hprev : δ.vertices.length - 2 < δ.vertices.length := by
            have hlen := δ.length_ge_two
            omega
          Metric.ball δ.target (targetRayRadius f) ∩ δ.carrier ⊆
            {y | ∃ c : ℝ, 0 ≤ c ∧
              y = δ.target +
                c • (δ.vertices[δ.vertices.length - 2]'hprev - δ.target)} := by
      intro f
      dsimp [targetRayRadius]
      exact (Classical.choose_spec
        (PolygonalArcTargetEndpointRayCover (D.edgeArc f))).2
    let edgeDir : G.edgeFinset → EuclideanSpace ℝ (Fin 2) := fun f =>
      let δ := D.edgeArc f
      let hfirst : 1 < δ.vertices.length :=
        Nat.lt_of_succ_le δ.length_ge_two
      let hprev : δ.vertices.length - 2 < δ.vertices.length := by
        have hlen := δ.length_ge_two
        omega
      if x = δ.source then
        δ.vertices[1]'hfirst - x
      else
        δ.vertices[δ.vertices.length - 2]'hprev - x
    have carrier_vertex_endpoint :
        ∀ f : G.edgeFinset, x ∈ (D.edgeArc f).carrier →
          x = (D.edgeArc f).source ∨ x = (D.edgeArc f).target := by
      intro f hxcar
      rcases hx_vertex with ⟨u, hxu⟩
      have hxnotrel : x ∉ (D.edgeArc f).relativeInterior := by
        intro hxrel
        exact D.no_vertex_in_edge_interior u f (by simpa [hxu] using hxrel)
      by_contra hnot
      have hnot_source : x ≠ (D.edgeArc f).source := by
        intro hs
        exact hnot (Or.inl hs)
      have hnot_target : x ≠ (D.edgeArc f).target := by
        intro ht
        exact hnot (Or.inr ht)
      have hxrel : x ∈ (D.edgeArc f).relativeInterior := by
        rw [(D.edgeArc f).relativeInterior_eq]
        refine ⟨hxcar, ?_⟩
        simp [hnot_source, hnot_target]
      exact hxnotrel hxrel
    let edgeRadius : G.edgeFinset → ℝ := fun f =>
      if hxcar : x ∈ (D.edgeArc f).carrier then
        if x = (D.edgeArc f).source then
          sourceRayRadius f
        else
          targetRayRadius f
      else
        Metric.infDist x (D.edgeArc f).carrier / 2
    have edgeRadius_pos : ∀ f : G.edgeFinset, 0 < edgeRadius f := by
      intro f
      by_cases hxcar : x ∈ (D.edgeArc f).carrier
      · by_cases hs : x = (D.edgeArc f).source
        · dsimp [edgeRadius]
          rw [if_pos hxcar, if_pos hs]
          exact sourceRayRadius_pos f
        · dsimp [edgeRadius]
          rw [if_pos hxcar, if_neg hs]
          exact targetRayRadius_pos f
      · have hcompact := PolygonalArcCarrierCompact (D.edgeArc f)
        have hnonempty : (D.edgeArc f).carrier.Nonempty :=
          ⟨(D.edgeArc f).source, source_mem_carrier (D.edgeArc f)⟩
        have hinf_pos : 0 < Metric.infDist x (D.edgeArc f).carrier :=
          (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hxcar
        dsimp [edgeRadius]
        rw [if_neg hxcar]
        exact half_pos hinf_pos
    have edgeRadius_spec :
        ∀ f : G.edgeFinset, f ≠ e →
          ∀ y : EuclideanSpace ℝ (Fin 2),
            y ∈ Metric.ball x (edgeRadius f) →
              y ∈ (D.edgeArc f).carrier →
                x ∈ (D.edgeArc f).carrier ∧
                  ∃ c : ℝ, 0 ≤ c ∧ y = x + c • edgeDir f := by
      intro f _hfe y hyball hycar
      by_cases hxcar : x ∈ (D.edgeArc f).carrier
      · have hxendpoint := carrier_vertex_endpoint f hxcar
        by_cases hs : x = (D.edgeArc f).source
        · have hyball' : y ∈ Metric.ball x (sourceRayRadius f) := by
            have hr_eq : edgeRadius f = sourceRayRadius f := by
              dsimp [edgeRadius]
              rw [if_pos hxcar, if_pos hs]
            simpa [hr_eq] using hyball
          have hyball_source :
              y ∈ Metric.ball (D.edgeArc f).source (sourceRayRadius f) := by
            simpa [hs] using hyball'
          have hyray := sourceRayRadius_spec f ⟨hyball_source, hycar⟩
          rcases hyray with ⟨c, hc, hy_eq⟩
          refine ⟨hxcar, c, hc, ?_⟩
          simpa [edgeDir, hs] using hy_eq
        · have hxtarget : x = (D.edgeArc f).target := by
            rcases hxendpoint with hxs | hxt
            · exact False.elim (hs hxs)
            · exact hxt
          have htarget_ne_source :
              (D.edgeArc f).target ≠ (D.edgeArc f).source := by
            intro hts
            exact hs (by rw [hxtarget, hts])
          have hyball' : y ∈ Metric.ball x (targetRayRadius f) := by
            have hr_eq : edgeRadius f = targetRayRadius f := by
              dsimp [edgeRadius]
              rw [if_pos hxcar, if_neg hs]
            simpa [hr_eq] using hyball
          have hyball_target :
              y ∈ Metric.ball (D.edgeArc f).target (targetRayRadius f) := by
            simpa [hxtarget] using hyball'
          have hyray := targetRayRadius_spec f ⟨hyball_target, hycar⟩
          rcases hyray with ⟨c, hc, hy_eq⟩
          refine ⟨hxcar, c, hc, ?_⟩
          simpa [edgeDir, hxtarget, htarget_ne_source] using hy_eq
      · exfalso
        have hcompact := PolygonalArcCarrierCompact (D.edgeArc f)
        have hnonempty : (D.edgeArc f).carrier.Nonempty :=
          ⟨(D.edgeArc f).source, source_mem_carrier (D.edgeArc f)⟩
        have hinf_pos : 0 < Metric.infDist x (D.edgeArc f).carrier :=
          (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hxcar
        have hedge_lt :
            edgeRadius f < Metric.infDist x (D.edgeArc f).carrier := by
          dsimp [edgeRadius]
          rw [if_neg hxcar]
          exact half_lt_self hinf_pos
        have hy_lt_edge : dist x y < edgeRadius f := by
          simpa [dist_comm] using (Metric.mem_ball.mp hyball)
        have hinf_le : Metric.infDist x (D.edgeArc f).carrier ≤ dist x y :=
          Metric.infDist_le_dist_of_mem hycar
        linarith
    let vertexRadius : V → ℝ := fun v =>
      if D.vertexPlacement v = x then
        1
      else
        dist x (D.vertexPlacement v) / 2
    have vertexRadius_pos : ∀ v : V, 0 < vertexRadius v := by
      intro v
      by_cases hvx : D.vertexPlacement v = x
      · simp [vertexRadius, hvx]
      · have hdist_pos : 0 < dist x (D.vertexPlacement v) := by
          exact dist_pos.mpr (by exact fun h => hvx h.symm)
        simp [vertexRadius, hvx, half_pos hdist_pos]
    rcases hx_vertex with ⟨u₀, hu₀⟩
    let vertexInf : ℝ :=
      Finset.univ.inf'
        (show (Finset.univ : Finset V).Nonempty from
          ⟨u₀, Finset.mem_univ u₀⟩)
        vertexRadius
    have vertexInf_pos : 0 < vertexInf := by
      dsimp [vertexInf]
      exact (Finset.lt_inf'_iff _).2 (by
        intro v _hv
        exact vertexRadius_pos v)
    have vertexInf_le :
        ∀ v : V, vertexInf ≤ vertexRadius v := by
      intro v
      dsimp [vertexInf]
      exact Finset.inf'_le vertexRadius (Finset.mem_univ v)
    let edgeInf : ℝ :=
      Finset.univ.inf'
        (show (Finset.univ : Finset G.edgeFinset).Nonempty from
          ⟨e, Finset.mem_univ e⟩)
        edgeRadius
    have edgeInf_pos : 0 < edgeInf := by
      dsimp [edgeInf]
      exact (Finset.lt_inf'_iff _).2 (by
        intro f _hf
        exact edgeRadius_pos f)
    have edgeInf_le :
        ∀ f : G.edgeFinset, edgeInf ≤ edgeRadius f := by
      intro f
      dsimp [edgeInf]
      exact Finset.inf'_le edgeRadius (Finset.mem_univ f)
    let r : ℝ := min vertexInf edgeInf
    have hr_pos : 0 < r := lt_min vertexInf_pos edgeInf_pos
    let incidentEdges : Finset G.edgeFinset :=
      Finset.univ.filter
        (fun f : G.edgeFinset => f ≠ e ∧ x ∈ (D.edgeArc f).carrier)
    let directions : Finset (EuclideanSpace ℝ (Fin 2)) :=
      incidentEdges.image edgeDir
    have directions_no_pos :
        ∀ v ∈ directions, ¬ ∃ a : ℝ, 0 < a ∧ v = a • d := by
      intro v hv
      rw [Finset.mem_image] at hv
      rcases hv with ⟨f, hfmem, rfl⟩
      have hfprops : f ≠ e ∧ x ∈ (D.edgeArc f).carrier := by
        simpa [incidentEdges] using hfmem
      rcases hfprops with ⟨hfe, hxcar⟩
      by_cases hs : x = (D.edgeArc f).source
      · have hfirstf : 0 + 1 < (D.edgeArc f).vertices.length := by
          have hlen := (D.edgeArc f).length_ge_two
          omega
        have h0f : 0 < (D.edgeArc f).vertices.length := by
          have hlen := (D.edgeArc f).length_ge_two
          omega
        have hsource0f : (D.edgeArc f).vertices[0] = (D.edgeArc f).source := by
          have hget :
              (D.edgeArc f).vertices[0]? = some (D.edgeArc f).vertices[0] :=
            List.getElem?_eq_getElem h0f
          rw [← List.head?_eq_getElem?, (D.edgeArc f).source_eq_head] at hget
          exact Option.some.inj hget.symm
        have hsegf :
            segment ℝ x (x + edgeDir f) =
              segment ℝ (D.edgeArc f).vertices[0]
                (D.edgeArc f).vertices[0 + 1] := by
          have hadd :
              x + ((D.edgeArc f).vertices[1]'(by
                have hlen := (D.edgeArc f).length_ge_two
                omega) - x) = (D.edgeArc f).vertices[1]'(by
                have hlen := (D.edgeArc f).length_ge_two
                omega) := by
            abel
          simpa [edgeDir, hs, hsource0f, hadd]
        exact OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
          G D (e := e) (f := f) hfe.symm hiSel hfirstf hd hsegSel hsegf
      · have hxendpoint := carrier_vertex_endpoint f hxcar
        have hxtarget : x = (D.edgeArc f).target := by
          rcases hxendpoint with hxs | hxt
          · exact False.elim (hs hxs)
          · exact hxt
        have htarget_ne_source :
            (D.edgeArc f).target ≠ (D.edgeArc f).source := by
          intro hts
          exact hs (by rw [hxtarget, hts])
        let jlast : ℕ := (D.edgeArc f).vertices.length - 2
        have hjlast : jlast + 1 < (D.edgeArc f).vertices.length := by
          have hlen := (D.edgeArc f).length_ge_two
          dsimp [jlast]
          omega
        have hlast_lt :
            (D.edgeArc f).vertices.length - 1 <
              (D.edgeArc f).vertices.length := by
          have hlen := (D.edgeArc f).length_ge_two
          omega
        have hlast_succ : jlast + 1 = (D.edgeArc f).vertices.length - 1 := by
          have hlen := (D.edgeArc f).length_ge_two
          dsimp [jlast]
          omega
        have htarget_last :
            (D.edgeArc f).vertices[jlast + 1] = (D.edgeArc f).target := by
          have hget :
              (D.edgeArc f).vertices[(D.edgeArc f).vertices.length - 1]? =
                some ((D.edgeArc f).vertices[(D.edgeArc f).vertices.length - 1]) :=
            List.getElem?_eq_getElem hlast_lt
          rw [← List.getLast?_eq_getElem?, (D.edgeArc f).target_eq_last] at hget
          have hlast_vertex :
              (D.edgeArc f).vertices[(D.edgeArc f).vertices.length - 1] =
                (D.edgeArc f).target :=
            Option.some.inj hget.symm
          simpa [hlast_succ] using hlast_vertex
        have hsegf :
            segment ℝ x (x + edgeDir f) =
              segment ℝ (D.edgeArc f).vertices[jlast]
                (D.edgeArc f).vertices[jlast + 1] := by
          have hadd :
              x + ((D.edgeArc f).vertices[jlast]'(by
                have hlen := (D.edgeArc f).length_ge_two
                dsimp [jlast]
                omega) - x) = (D.edgeArc f).vertices[jlast]'(by
                have hlen := (D.edgeArc f).length_ge_two
                dsimp [jlast]
                omega) := by
            abel
          simpa [edgeDir, hxtarget, htarget_ne_source, htarget_last, hadd, jlast,
            segment_symm]
        exact OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
          G D (e := e) (f := f) hfe.symm hiSel hjlast hd hsegSel hsegf
    refine ⟨r, hr_pos, directions, directions_no_pos, ?_⟩
    intro y hy
    rcases hy with ⟨hyball, hyimg⟩
    rw [OrdinaryDrawingImageWithoutEdge] at hyimg
    rcases hyimg with hyvertex | hyedge
    · rcases hyvertex with ⟨v, rfl⟩
      by_cases hvx : D.vertexPlacement v = x
      · exact Or.inl (by simpa [hvx])
      · exfalso
        have hyle : r ≤ vertexRadius v := by
          exact le_trans (min_le_left vertexInf edgeInf) (vertexInf_le v)
        have hy_lt_vertex : dist x (D.vertexPlacement v) < vertexRadius v := by
          have hy_lt_r : dist x (D.vertexPlacement v) < r := by
            simpa [dist_comm] using (Metric.mem_ball.mp hyball)
          exact lt_of_lt_of_le hy_lt_r hyle
        have hnonneg : 0 ≤ dist x (D.vertexPlacement v) := dist_nonneg
        simp [vertexRadius, hvx] at hy_lt_vertex
        linarith
    · rcases Set.mem_iUnion.mp hyedge with ⟨f, hyf⟩
      let f' : G.edgeFinset := f.1
      have hfe : f' ≠ e := f.2
      have hyle : r ≤ edgeRadius f' := by
        exact le_trans (min_le_right vertexInf edgeInf) (edgeInf_le f')
      have hyball_edge : y ∈ Metric.ball x (edgeRadius f') := by
        have hy_lt_r : dist y x < r := Metric.mem_ball.mp hyball
        exact Metric.mem_ball.mpr (lt_of_lt_of_le hy_lt_r hyle)
      have hspec := edgeRadius_spec f' hfe y hyball_edge hyf
      rcases hspec with ⟨hxcar, c, hc, hy_eq⟩
      exact Or.inr (by
        have hfmem : f' ∈ incidentEdges := by
          simp [incidentEdges, hfe, hxcar]
        have hdir_mem : edgeDir f' ∈ directions := by
          exact Finset.mem_image.mpr ⟨f', hfmem, rfl⟩
        refine Set.mem_iUnion.2 ⟨⟨edgeDir f', hdir_mem⟩, ?_⟩
        exact ⟨c, hc, hy_eq⟩)
  have hfirstγ : 0 + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  have h0γ : 0 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  have hsource0γ : γ.vertices[0] = γ.source := by
    have hget : γ.vertices[0]? = some γ.vertices[0] :=
      List.getElem?_eq_getElem h0γ
    rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
    exact Option.some.inj hget.symm
  let d₀ : EuclideanSpace ℝ (Fin 2) := γ.vertices[1]'hfirstγ - γ.source
  have hd₀ : d₀ ≠ 0 := by
    have hp_ne : γ.vertices[1]'hfirstγ ≠ γ.source := by
      intro hp
      have hidx : (1 : ℕ) = 0 := by
        have hEq :
            γ.vertices[1]'hfirstγ = γ.vertices[0]'h0γ := by
          simpa [hsource0γ] using hp
        exact (γ.simple_vertices.getElem_inj_iff).mp hEq
      omega
    dsimp [d₀]
    exact sub_ne_zero.mpr hp_ne
  have hiSel₀ : 0 + 1 < (D.edgeArc e).vertices.length := by
    simpa [hγ] using hfirstγ
  have hsegSel₀ :
      segment ℝ γ.source (γ.source + d₀) =
        segment ℝ (D.edgeArc e).vertices[0] (D.edgeArc e).vertices[0 + 1] := by
    have hadd : γ.source + d₀ = γ.vertices[1]'hfirstγ := by
      dsimp [d₀]
      abel
    simpa [hγ, hsource0γ, hadd]
  obtain ⟨r₀, hr₀, initialDirections, hinit_no_pos, hinit_cover⟩ :=
    endpointCover γ.source d₀ hd₀ hsource_vertex 0 hiSel₀ hsegSel₀
  let jlast : ℕ := γ.vertices.length - 2
  have hjlast : jlast + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    dsimp [jlast]
    omega
  have hlast_lt : γ.vertices.length - 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  have hlast_succ : jlast + 1 = γ.vertices.length - 1 := by
    have hlen := γ.length_ge_two
    dsimp [jlast]
    omega
  have htarget_lastγ : γ.vertices[jlast + 1] = γ.target := by
    have hget :
        γ.vertices[γ.vertices.length - 1]? =
          some (γ.vertices[γ.vertices.length - 1]) :=
      List.getElem?_eq_getElem hlast_lt
    rw [← List.getLast?_eq_getElem?, γ.target_eq_last] at hget
    have hlast_vertex : γ.vertices[γ.vertices.length - 1] = γ.target :=
      Option.some.inj hget.symm
    simpa [hlast_succ] using hlast_vertex
  let d₁ : EuclideanSpace ℝ (Fin 2) := γ.vertices[jlast]'(by
      have hlen := γ.length_ge_two
      dsimp [jlast]
      omega) - γ.target
  have hd₁ : d₁ ≠ 0 := by
    have hp_ne :
        γ.vertices[jlast]'(by
          have hlen := γ.length_ge_two
          dsimp [jlast]
          omega) ≠ γ.target := by
      intro hp
      have hidx : jlast = jlast + 1 := by
        have hjlt : jlast < γ.vertices.length := Nat.lt_of_succ_lt hjlast
        have hEq :
            γ.vertices[jlast]'hjlt = γ.vertices[jlast + 1]'hjlast := by
          simpa [htarget_lastγ] using hp
        exact (γ.simple_vertices.getElem_inj_iff).mp hEq
      omega
    dsimp [d₁]
    exact sub_ne_zero.mpr hp_ne
  have hiSel₁ : jlast + 1 < (D.edgeArc e).vertices.length := by
    simpa [hγ] using hjlast
  have hsegSel₁ :
      segment ℝ γ.target (γ.target + d₁) =
        segment ℝ (D.edgeArc e).vertices[jlast]
          (D.edgeArc e).vertices[jlast + 1] := by
    have hadd :
        γ.target + d₁ = γ.vertices[jlast]'(by
          have hlen := γ.length_ge_two
          dsimp [jlast]
          omega) := by
      dsimp [d₁]
      abel
    simpa [hγ, htarget_lastγ, hadd, segment_symm]
  obtain ⟨r₁, hr₁, terminalDirections, hterm_no_pos, hterm_cover⟩ :=
    endpointCover γ.target d₁ hd₁ htarget_vertex jlast hiSel₁ hsegSel₁
  refine ⟨r₀, r₁, hr₀, hr₁, initialDirections, terminalDirections, ?_, ?_, ?_, ?_⟩
  · simpa [d₀] using hinit_no_pos
  · simpa [d₁, jlast] using hterm_no_pos
  · simpa [d₀] using hinit_cover
  · simpa [d₁, jlast] using hterm_cover
