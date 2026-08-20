import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PlaneDrawingDartArcData

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartFirstGermsForRadii]
lemma PlaneDrawingDartFirstGermsForRadii {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D)
    (R : V → ℝ) (hR : ∀ v : V, 0 < R v) :
    ∃ germDirection :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2),
      ∃ radialGerm :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
          Set (EuclideanSpace ℝ (Fin 2)),
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d ≠ 0) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          ∃ r : ℝ, 0 < r ∧ r ≤ R v ∧
            radialGerm v d =
              openSegment ℝ (D.vertexPlacement v)
                (D.vertexPlacement v + r • germDirection v d)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d ⊆ (D.edgeArc (A.dartEdge d.1)).carrier) := by
-- BODY
  classical
  let firstDirection :
      ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2) :=
    fun v d =>
      let hfirst : 1 < (A.dartArc d.1).vertices.length :=
        Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two
      (A.dartArc d.1).vertices[1]'hfirst - D.vertexPlacement v
  let shortRadius : V → ℝ := fun v => min (R v / 2) (1 / 2 : ℝ)
  let firstGerm :
      ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
        Set (EuclideanSpace ℝ (Fin 2)) :=
    fun v d =>
      openSegment ℝ (D.vertexPlacement v)
        (D.vertexPlacement v + shortRadius v • firstDirection v d)
  refine ⟨firstDirection, firstGerm, ?_, ?_, ?_⟩
  · intro v d
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
  · intro v d
    refine ⟨shortRadius v, ?_, ?_, rfl⟩
    · dsimp [shortRadius]
      have hhalf : 0 < R v / 2 := by nlinarith [hR v]
      norm_num [hhalf]
    · dsimp [shortRadius]
      have hhalf_le : R v / 2 ≤ R v := by nlinarith [hR v]
      exact (min_le_left (R v / 2) (1 / 2 : ℝ)).trans hhalf_le
  · intro v d x hx
    dsimp [firstGerm, firstDirection] at hx
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
    have hshort_nonneg : 0 ≤ shortRadius v := by
      have hpos : 0 < shortRadius v := by
        dsimp [shortRadius]
        have hhalf : 0 < R v / 2 := by nlinarith [hR v]
        norm_num [hhalf]
      exact le_of_lt hpos
    have hshort_le_one : shortRadius v ≤ 1 := by
      have hle : shortRadius v ≤ (1 / 2 : ℝ) := by
        dsimp [shortRadius]
        exact min_le_right (R v / 2) (1 / 2 : ℝ)
      norm_num at hle ⊢
      linarith
    have hend_mem :
        D.vertexPlacement v +
            shortRadius v • ((A.dartArc d.1).vertices[1] - D.vertexPlacement v) ∈
          segment ℝ (D.vertexPlacement v) γ.vertices[1] := by
      rw [segment_eq_image_lineMap]
      refine ⟨shortRadius v, ⟨hshort_nonneg, hshort_le_one⟩, ?_⟩
      rw [AffineMap.lineMap_apply_module]
      dsimp [γ]
      module
    have hxseg :
        x ∈ segment ℝ (D.vertexPlacement v) γ.vertices[1] := by
      have hxsmall :
          x ∈ segment ℝ (D.vertexPlacement v)
              (D.vertexPlacement v +
                shortRadius v • ((A.dartArc d.1).vertices[1] - D.vertexPlacement v)) :=
        openSegment_subset_segment ℝ _ _ hx
      exact (convex_segment (𝕜 := ℝ) (D.vertexPlacement v) γ.vertices[1]).segment_subset
        (left_mem_segment ℝ (D.vertexPlacement v) γ.vertices[1]) hend_mem hxsmall
    have hx_arc : x ∈ γ.carrier := by
      rw [γ.carrier_eq]
      refine ⟨0, ?_, ?_⟩
      · simpa [γ] using hfirst
      · simpa [γ, hzero_vertex] using hxseg
    simpa [γ, A.dartArc_carrier d.1] using hx_arc
