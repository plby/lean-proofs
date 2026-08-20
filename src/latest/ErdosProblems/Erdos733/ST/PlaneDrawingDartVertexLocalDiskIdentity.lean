import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.CrossingFreeEdgeInteriorDisjoint
import ErdosProblems.Erdos733.ST.OrdinaryDrawingImage
import ErdosProblems.Erdos733.ST.OrdinaryDrawingSegmentDirectionsNotSamePositiveRay
import ErdosProblems.Erdos733.ST.PlaneDrawingDartArcData
import ErdosProblems.Erdos733.ST.PlaneDrawingDartSourceEndpointRayCovers
import ErdosProblems.Erdos733.ST.PlaneDrawingDartUnitFirstGermsForRadii
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalArcCarrierCompact
import ErdosProblems.Erdos733.ST.PositiveSeparation

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartVertexLocalDiskIdentity]
lemma PlaneDrawingDartVertexLocalDiskIdentity {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    ∃ localDiskRadius : V → ℝ,
      ∃ germDirection :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2),
      ∃ radialGerm :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
          Set (EuclideanSpace ℝ (Fin 2)),
        (∀ v : V, 0 < localDiskRadius v) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d ≠ 0) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d =
            (‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v‖)⁻¹ •
              ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d =
            openSegment ℝ (D.vertexPlacement v)
              (D.vertexPlacement v + localDiskRadius v • germDirection v d)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d ⊆ (D.edgeArc (A.dartEdge d.1)).carrier) ∧
        (∀ v : V,
          Metric.ball (D.vertexPlacement v) (localDiskRadius v) ∩
              OrdinaryDrawingImage G D =
            {D.vertexPlacement v} ∪
              ⋃ d : {d : G.Dart // d.toProd.1 = v}, radialGerm v d) := by
-- BODY
  classical
  have _hD : D.crossingSet.card = 0 := hD
  have source_mem_carrier :
      ∀ γ : PolygonalArc, γ.source ∈ γ.carrier := by
    intro γ
    rw [γ.carrier_eq]
    have h0 : 0 < γ.vertices.length := by
      have hlen := γ.length_ge_two
      omega
    have hfirst : 0 + 1 < γ.vertices.length := by
      have hlen := γ.length_ge_two
      omega
    have hsource0 : γ.vertices[0] = γ.source := by
      have hget : γ.vertices[0]? = some γ.vertices[0] :=
        List.getElem?_eq_getElem h0
      rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
      exact Option.some.inj hget.symm
    exact ⟨0, hfirst, by simpa [hsource0] using
      (left_mem_segment ℝ γ.vertices[0] γ.vertices[0 + 1])⟩
  have carrier_vertex_endpoint :
      ∀ (v : V) (e : G.edgeFinset),
        D.vertexPlacement v ∈ (D.edgeArc e).carrier →
          D.vertexPlacement v = (D.edgeArc e).source ∨
            D.vertexPlacement v = (D.edgeArc e).target := by
    intro v e hvcar
    have hvnotrel : D.vertexPlacement v ∉ (D.edgeArc e).relativeInterior :=
      D.no_vertex_in_edge_interior v e
    by_contra hnot
    have hnot_source : D.vertexPlacement v ≠ (D.edgeArc e).source := by
      intro hs
      exact hnot (Or.inl hs)
    have hnot_target : D.vertexPlacement v ≠ (D.edgeArc e).target := by
      intro ht
      exact hnot (Or.inr ht)
    have hvrel : D.vertexPlacement v ∈ (D.edgeArc e).relativeInterior := by
      rw [(D.edgeArc e).relativeInterior_eq]
      exact ⟨hvcar, by simp [hnot_source, hnot_target]⟩
    exact hvnotrel hvrel
  have carrier_vertex_outgoing_dart :
      ∀ (v : V) (e : G.edgeFinset),
        D.vertexPlacement v ∈ (D.edgeArc e).carrier →
          ∃ d : {d : G.Dart // d.toProd.1 = v}, A.dartEdge d.1 = e := by
    intro v e hvcar
    have hvendpoint := carrier_vertex_endpoint v e hvcar
    rcases D.edgeArc_endpoints e with ⟨u, w, huw, hedge, hends⟩
    rcases hends with hdir | hdir
    · rcases hdir with ⟨hsource, htarget⟩
      rcases hvendpoint with hvsource | hvtarget
      · have hvu : v = u := D.vertexPlacement_injective (hvsource.trans hsource)
        let d : G.Dart := ⟨(v, w), by simpa [hvu] using huw⟩
        refine ⟨⟨d, rfl⟩, ?_⟩
        apply Subtype.ext
        calc
          (A.dartEdge d).1 = d.edge := A.dartEdge_eq d
          _ = e.1 := by
            dsimp [d, SimpleGraph.Dart.edge]
            simpa [hvu] using hedge.symm
      · have hvw : v = w := D.vertexPlacement_injective (hvtarget.trans htarget)
        let d : G.Dart := ⟨(v, u), by simpa [hvw] using huw.symm⟩
        refine ⟨⟨d, rfl⟩, ?_⟩
        apply Subtype.ext
        calc
          (A.dartEdge d).1 = d.edge := A.dartEdge_eq d
          _ = e.1 := by
            dsimp [d, SimpleGraph.Dart.edge]
            simpa [hvw, Sym2.eq_swap] using hedge.symm
    · rcases hdir with ⟨hsource, htarget⟩
      rcases hvendpoint with hvsource | hvtarget
      · have hvw : v = w := D.vertexPlacement_injective (hvsource.trans hsource)
        let d : G.Dart := ⟨(v, u), by simpa [hvw] using huw.symm⟩
        refine ⟨⟨d, rfl⟩, ?_⟩
        apply Subtype.ext
        calc
          (A.dartEdge d).1 = d.edge := A.dartEdge_eq d
          _ = e.1 := by
            dsimp [d, SimpleGraph.Dart.edge]
            simpa [hvw, Sym2.eq_swap] using hedge.symm
      · have hvu : v = u := D.vertexPlacement_injective (hvtarget.trans htarget)
        let d : G.Dart := ⟨(v, w), by simpa [hvu] using huw⟩
        refine ⟨⟨d, rfl⟩, ?_⟩
        apply Subtype.ext
        calc
          (A.dartEdge d).1 = d.edge := A.dartEdge_eq d
          _ = e.1 := by
            dsimp [d, SimpleGraph.Dart.edge]
            simpa [hvu] using hedge.symm
  let firstDirection :
      ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2) :=
    fun v d =>
      let hfirst : 1 < (A.dartArc d.1).vertices.length :=
        Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two
      (A.dartArc d.1).vertices[1]'hfirst - D.vertexPlacement v
  have firstDirection_ne_zero :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        firstDirection v d ≠ 0 := by
    intro v d
    dsimp [firstDirection]
    let γ : PolygonalArc := A.dartArc d.1
    have hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
    have hzero : 0 < γ.vertices.length := by
      have hlen := γ.length_ge_two
      omega
    have hsource_vertex : γ.vertices[0] = γ.source := by
      have hget : γ.vertices[0]? = some γ.vertices[0] :=
        List.getElem?_eq_getElem hzero
      rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
      exact Option.some.inj hget.symm
    have hsource_v : γ.source = D.vertexPlacement v := by
      simpa [γ, d.2] using A.dartArc_source d.1
    have hzero_vertex : γ.vertices[0] = D.vertexPlacement v := by
      simpa [hsource_v] using hsource_vertex
    intro hq
    have h1eq0 : γ.vertices[1] = γ.vertices[0] := by
      have h1eqv : γ.vertices[1] = D.vertexPlacement v := by
        have htmp : γ.vertices[1] - D.vertexPlacement v = 0 := by
          simpa [γ] using hq
        exact sub_eq_zero.mp htmp
      exact h1eqv.trans hzero_vertex.symm
    have hidx : (1 : ℕ) = 0 := by
      exact γ.simple_vertices.getElem_inj_iff.mp h1eq0
    omega
  obtain ⟨sourceRayRadius, sourceRayRadius_pos, sourceRayRadius_spec⟩ :=
    PlaneDrawingDartSourceEndpointRayCovers G D A
  let vertexRadius : V → V → ℝ := fun v w =>
    if w = v then 1 else dist (D.vertexPlacement v) (D.vertexPlacement w) / 2
  have vertexRadius_pos : ∀ v w : V, 0 < vertexRadius v w := by
    intro v w
    by_cases hwv : w = v
    · simp [vertexRadius, hwv]
    · have hdist_pos : 0 < dist (D.vertexPlacement v) (D.vertexPlacement w) := by
        exact dist_pos.mpr (by
          intro h
          exact hwv ((D.vertexPlacement_injective h).symm))
      simp [vertexRadius, hwv, half_pos hdist_pos]
  let vertexInf : V → ℝ := fun v =>
    Finset.univ.inf'
      (show (Finset.univ : Finset V).Nonempty from ⟨v, Finset.mem_univ v⟩)
      (vertexRadius v)
  have vertexInf_pos : ∀ v : V, 0 < vertexInf v := by
    intro v
    dsimp [vertexInf]
    exact (Finset.lt_inf'_iff _).2 (by
      intro w _hw
      exact vertexRadius_pos v w)
  have vertexInf_le : ∀ v w : V, vertexInf v ≤ vertexRadius v w := by
    intro v w
    dsimp [vertexInf]
    exact Finset.inf'_le (vertexRadius v) (Finset.mem_univ w)
  let edgeRadius : V → G.edgeFinset → ℝ := fun v e =>
    if D.vertexPlacement v ∈ (D.edgeArc e).carrier then
      1
    else
      Metric.infDist (D.vertexPlacement v) (D.edgeArc e).carrier / 2
  have edgeRadius_pos : ∀ (v : V) (e : G.edgeFinset), 0 < edgeRadius v e := by
    intro v e
    by_cases hvcar : D.vertexPlacement v ∈ (D.edgeArc e).carrier
    · simp [edgeRadius, hvcar]
    · have hcompact := PolygonalArcCarrierCompact (D.edgeArc e)
      have hnonempty : (D.edgeArc e).carrier.Nonempty :=
        ⟨(D.edgeArc e).source, source_mem_carrier (D.edgeArc e)⟩
      have hinf_pos :
          0 < Metric.infDist (D.vertexPlacement v) (D.edgeArc e).carrier :=
        (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hvcar
      simp [edgeRadius, hvcar, half_pos hinf_pos]
  let edgeInf : V → ℝ := fun v =>
    if h : G.edgeFinset.attach.Nonempty then
      G.edgeFinset.attach.inf' h (edgeRadius v)
    else
      1
  have edgeInf_pos : ∀ v : V, 0 < edgeInf v := by
    intro v
    dsimp [edgeInf]
    by_cases h : G.edgeFinset.attach.Nonempty
    · rw [dif_pos h]
      exact (Finset.lt_inf'_iff _).2 (by
        intro e _he
        exact edgeRadius_pos v e)
    · rw [dif_neg h]
      norm_num
  have edgeInf_le : ∀ (v : V) (e : G.edgeFinset), edgeInf v ≤ edgeRadius v e := by
    intro v e
    dsimp [edgeInf]
    rw [dif_pos (show G.edgeFinset.attach.Nonempty from ⟨e, by simp⟩)]
    exact Finset.inf'_le (edgeRadius v) (by simp)
  let dartBound :
      ∀ v : V, {d : G.Dart // d.toProd.1 = v} → ℝ :=
    fun v d => min (sourceRayRadius v d) ‖firstDirection v d‖
  have dartBound_pos :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}), 0 < dartBound v d := by
    intro v d
    exact lt_min (sourceRayRadius_pos v d)
      (norm_pos_iff.mpr (firstDirection_ne_zero v d))
  let outgoingInf : V → ℝ := fun v =>
    if h : (Finset.univ : Finset {d : G.Dart // d.toProd.1 = v}).Nonempty then
      Finset.univ.inf' h (dartBound v)
    else
      1
  have outgoingInf_pos : ∀ v : V, 0 < outgoingInf v := by
    intro v
    dsimp [outgoingInf]
    by_cases h : (Finset.univ : Finset {d : G.Dart // d.toProd.1 = v}).Nonempty
    · rw [dif_pos h]
      exact (Finset.lt_inf'_iff _).2 (by
        intro d _hd
        exact dartBound_pos v d)
    · rw [dif_neg h]
      norm_num
  have outgoingInf_le :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        outgoingInf v ≤ dartBound v d := by
    intro v d
    dsimp [outgoingInf]
    rw [dif_pos (show
      (Finset.univ : Finset {d : G.Dart // d.toProd.1 = v}).Nonempty from
        ⟨d, Finset.mem_univ d⟩)]
    exact Finset.inf'_le (dartBound v) (Finset.mem_univ d)
  let localDiskRadius : V → ℝ := fun v =>
    min (min (vertexInf v) (edgeInf v)) (outgoingInf v)
  have localDiskRadius_pos : ∀ v : V, 0 < localDiskRadius v := by
    intro v
    exact lt_min (lt_min (vertexInf_pos v) (edgeInf_pos v)) (outgoingInf_pos v)
  have localDiskRadius_le_vertex :
      ∀ v w : V, localDiskRadius v ≤ vertexRadius v w := by
    intro v w
    exact ((min_le_left (min (vertexInf v) (edgeInf v)) (outgoingInf v)).trans
      (min_le_left (vertexInf v) (edgeInf v))).trans (vertexInf_le v w)
  have localDiskRadius_le_edge :
      ∀ (v : V) (e : G.edgeFinset), localDiskRadius v ≤ edgeRadius v e := by
    intro v e
    exact ((min_le_left (min (vertexInf v) (edgeInf v)) (outgoingInf v)).trans
      (min_le_right (vertexInf v) (edgeInf v))).trans (edgeInf_le v e)
  have localDiskRadius_le_dartBound :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        localDiskRadius v ≤ dartBound v d := by
    intro v d
    exact (min_le_right (min (vertexInf v) (edgeInf v)) (outgoingInf v)).trans
      (outgoingInf_le v d)
  have localDiskRadius_le_sourceRay :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        localDiskRadius v ≤ sourceRayRadius v d := by
    intro v d
    exact (localDiskRadius_le_dartBound v d).trans
      (min_le_left (sourceRayRadius v d) ‖firstDirection v d‖)
  have localDiskRadius_le_first :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        localDiskRadius v ≤
          ‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
              (A.dartArc d.1).length_ge_two) - D.vertexPlacement v‖ := by
    intro v d
    change localDiskRadius v ≤ ‖firstDirection v d‖
    exact (localDiskRadius_le_dartBound v d).trans
      (min_le_right (sourceRayRadius v d) ‖firstDirection v d‖)
  rcases PlaneDrawingDartUnitFirstGermsForRadii G D A localDiskRadius
      localDiskRadius_pos localDiskRadius_le_first with
    ⟨germDirection, radialGerm, germDirection_ne_zero,
      germDirection_eq, _radialGerm_short, radialGerm_eq,
      radialGerm_subset, radialGerm_subset_ball⟩
  refine ⟨localDiskRadius, germDirection, radialGerm,
    localDiskRadius_pos, germDirection_ne_zero, germDirection_eq,
    radialGerm_eq, radialGerm_subset, ?_⟩
  intro v
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxball, hximage⟩
    by_cases hxv : x = D.vertexPlacement v
    · exact Or.inl (by simp [hxv])
    · rw [OrdinaryDrawingImage] at hximage
      rcases hximage with hxvertex | hxedge
      · rcases hxvertex with ⟨w, rfl⟩
        by_cases hwv : w = v
        · exact Or.inl (by simp [hwv])
        · exfalso
          have hlt_local :
              dist (D.vertexPlacement v) (D.vertexPlacement w) <
                localDiskRadius v := by
            simpa [dist_comm] using (Metric.mem_ball.mp hxball)
          have hlt_vertex :
              dist (D.vertexPlacement v) (D.vertexPlacement w) <
                vertexRadius v w :=
            lt_of_lt_of_le hlt_local (localDiskRadius_le_vertex v w)
          have hnonneg : 0 ≤ dist (D.vertexPlacement v) (D.vertexPlacement w) :=
            dist_nonneg
          dsimp [vertexRadius] at hlt_vertex
          rw [if_neg hwv] at hlt_vertex
          nlinarith
      · rcases Set.mem_iUnion.mp hxedge with ⟨e, hxe⟩
        by_cases hvcar : D.vertexPlacement v ∈ (D.edgeArc e).carrier
        · rcases carrier_vertex_outgoing_dart v e hvcar with ⟨d, hdedge⟩
          have hxball_source :
              x ∈ Metric.ball (D.vertexPlacement v) (sourceRayRadius v d) := by
            exact Metric.mem_ball.mpr
              (lt_of_lt_of_le (Metric.mem_ball.mp hxball)
                (localDiskRadius_le_sourceRay v d))
          have hxe_dart :
              x ∈ (D.edgeArc (A.dartEdge d.1)).carrier := by
            simpa [hdedge] using hxe
          have hxray := sourceRayRadius_spec v d ⟨hxball_source, hxe_dart⟩
          rcases hxray with ⟨c, hc_nonneg, hxray⟩
          have hxray' :
              x = D.vertexPlacement v + c • firstDirection v d := by
            simpa [firstDirection] using hxray
          have hc_ne_zero : c ≠ 0 := by
            intro hc
            have hx_eq_v : x = D.vertexPlacement v := by
              simpa [hc] using hxray'
            exact hxv hx_eq_v
          have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc_ne_zero)
          have hq_pos : 0 < ‖firstDirection v d‖ :=
            norm_pos_iff.mpr (firstDirection_ne_zero v d)
          have hdist_eq :
              dist x (D.vertexPlacement v) = c * ‖firstDirection v d‖ := by
            rw [hxray', dist_eq_norm]
            have hsub :
                D.vertexPlacement v + c • firstDirection v d -
                    D.vertexPlacement v =
                  c • firstDirection v d := by
              module
            rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
          have hdist_lt :
              c * ‖firstDirection v d‖ < localDiskRadius v := by
            simpa [hdist_eq] using (Metric.mem_ball.mp hxball)
          let t : ℝ := c * ‖firstDirection v d‖ / localDiskRadius v
          have ht_pos : 0 < t := by
            dsimp [t]
            exact div_pos (mul_pos hc_pos hq_pos) (localDiskRadius_pos v)
          have ht_lt_one : t < 1 := by
            dsimp [t]
            rw [div_lt_one (localDiskRadius_pos v)]
            exact hdist_lt
          have hdir_eq :
              germDirection v d =
                (‖firstDirection v d‖)⁻¹ • firstDirection v d := by
            simpa [firstDirection] using germDirection_eq v d
          have hline :
              AffineMap.lineMap (D.vertexPlacement v)
                  (D.vertexPlacement v + localDiskRadius v • germDirection v d) t =
                x := by
            rw [hxray', hdir_eq, AffineMap.lineMap_apply_module]
            have hcoef :
                t * localDiskRadius v * (‖firstDirection v d‖)⁻¹ = c := by
              dsimp [t]
              field_simp [ne_of_gt (localDiskRadius_pos v), ne_of_gt hq_pos]
            calc
              (1 - t) • D.vertexPlacement v +
                  t • (D.vertexPlacement v +
                    localDiskRadius v •
                      ((‖firstDirection v d‖)⁻¹ • firstDirection v d))
                  =
                D.vertexPlacement v +
                  (t * localDiskRadius v * (‖firstDirection v d‖)⁻¹) •
                    firstDirection v d := by
                  module
              _ = D.vertexPlacement v + c • firstDirection v d := by
                  rw [hcoef]
          have hxopen :
              x ∈ openSegment ℝ (D.vertexPlacement v)
                (D.vertexPlacement v + localDiskRadius v • germDirection v d) := by
            have hmem :=
              lineMap_mem_openSegment (𝕜 := ℝ) (D.vertexPlacement v)
                (D.vertexPlacement v + localDiskRadius v • germDirection v d)
                ⟨ht_pos, ht_lt_one⟩
            simpa [hline] using hmem
          exact Or.inr (Set.mem_iUnion.2 ⟨d, by
            rw [radialGerm_eq v d]
            exact hxopen⟩)
        · exfalso
          have hlt_local :
              dist (D.vertexPlacement v) x < localDiskRadius v := by
            simpa [dist_comm] using (Metric.mem_ball.mp hxball)
          have hlt_edge :
              dist (D.vertexPlacement v) x < edgeRadius v e :=
            lt_of_lt_of_le hlt_local (localDiskRadius_le_edge v e)
          have hinf_le :
              Metric.infDist (D.vertexPlacement v) (D.edgeArc e).carrier ≤
                dist (D.vertexPlacement v) x :=
            Metric.infDist_le_dist_of_mem hxe
          have hinf_nonneg :
              0 ≤ Metric.infDist (D.vertexPlacement v) (D.edgeArc e).carrier :=
            Metric.infDist_nonneg
          dsimp [edgeRadius] at hlt_edge
          rw [if_neg hvcar] at hlt_edge
          nlinarith
  · intro x hx
    rcases hx with hxvertex | hxgerm
    · have hx_eq : x = D.vertexPlacement v := by
        simpa using hxvertex
      constructor
      · simpa [hx_eq, Metric.mem_ball] using localDiskRadius_pos v
      · rw [OrdinaryDrawingImage]
        exact Or.inl ⟨v, by simp [hx_eq]⟩
    · rcases Set.mem_iUnion.mp hxgerm with ⟨d, hxd⟩
      constructor
      · exact radialGerm_subset_ball v d hxd
      · rw [OrdinaryDrawingImage]
        exact Or.inr (Set.mem_iUnion.2
          ⟨A.dartEdge d.1, radialGerm_subset v d hxd⟩)
