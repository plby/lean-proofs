import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PlaneDrawingDartArcData

open Classical
noncomputable section

-- [TABLET NODE: PlaneDrawingDartUnitFirstGermsForRadii]
lemma PlaneDrawingDartUnitFirstGermsForRadii {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G)
    (A : PlaneDrawingDartArcData G D)
    (R : V → ℝ) (hR : ∀ v : V, 0 < R v)
    (hR_le_first :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        R v ≤ ‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le (A.dartArc d.1).length_ge_two) -
          D.vertexPlacement v‖) :
    ∃ germDirection :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2),
      ∃ radialGerm :
        ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
          Set (EuclideanSpace ℝ (Fin 2)),
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d ≠ 0) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          germDirection v d =
            (‖(A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v‖)⁻¹ •
              ((A.dartArc d.1).vertices[1]'(Nat.lt_of_succ_le
                  (A.dartArc d.1).length_ge_two) - D.vertexPlacement v)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          ∃ r : ℝ, 0 < r ∧ r ≤ R v ∧
            radialGerm v d =
              openSegment ℝ (D.vertexPlacement v)
                (D.vertexPlacement v + r • germDirection v d)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d =
            openSegment ℝ (D.vertexPlacement v)
              (D.vertexPlacement v + R v • germDirection v d)) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d ⊆ (D.edgeArc (A.dartEdge d.1)).carrier) ∧
        (∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
          radialGerm v d ⊆ Metric.ball (D.vertexPlacement v) (R v)) := by
-- BODY
  classical
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
  let unitDirection :
      ∀ v : V, {d : G.Dart // d.toProd.1 = v} → EuclideanSpace ℝ (Fin 2) :=
    fun v d => (‖firstDirection v d‖)⁻¹ • firstDirection v d
  let firstGerm :
      ∀ v : V, {d : G.Dart // d.toProd.1 = v} →
        Set (EuclideanSpace ℝ (Fin 2)) :=
    fun v d =>
      openSegment ℝ (D.vertexPlacement v)
        (D.vertexPlacement v + R v • unitDirection v d)
  refine ⟨unitDirection, firstGerm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v d hzero
    have hnorm_pos : 0 < ‖firstDirection v d‖ :=
      norm_pos_iff.mpr (firstDirection_ne_zero v d)
    have hscale_ne : (‖firstDirection v d‖)⁻¹ ≠ (0 : ℝ) :=
      inv_ne_zero (ne_of_gt hnorm_pos)
    rcases smul_eq_zero.mp hzero with hscale | hdir
    · exact hscale_ne hscale
    · exact firstDirection_ne_zero v d hdir
  · intro v d
    rfl
  · intro v d
    exact ⟨R v, hR v, le_rfl, rfl⟩
  · intro v d
    rfl
  · intro v d x hx
    dsimp [firstGerm, unitDirection, firstDirection] at hx
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
    have hq_pos : 0 < ‖firstDirection v d‖ :=
      norm_pos_iff.mpr (firstDirection_ne_zero v d)
    have hcoef_nonneg :
        0 ≤ R v * (‖firstDirection v d‖)⁻¹ := by
      exact mul_nonneg (le_of_lt (hR v)) (inv_nonneg.mpr (norm_nonneg _))
    have hcoef_le_one :
        R v * (‖firstDirection v d‖)⁻¹ ≤ 1 := by
      have hle : R v ≤ ‖firstDirection v d‖ := by
        simpa [firstDirection] using hR_le_first v d
      have hmul := mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr (le_of_lt hq_pos))
      have hright : ‖firstDirection v d‖ * (‖firstDirection v d‖)⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt hq_pos)
      simpa [hright] using hmul
    have hend_mem :
        D.vertexPlacement v +
            R v • ((‖firstDirection v d‖)⁻¹ • firstDirection v d) ∈
          segment ℝ (D.vertexPlacement v) γ.vertices[1] := by
      rw [segment_eq_image_lineMap]
      refine ⟨R v * (‖firstDirection v d‖)⁻¹, ⟨hcoef_nonneg, hcoef_le_one⟩, ?_⟩
      rw [AffineMap.lineMap_apply_module]
      dsimp [γ]
      dsimp [firstDirection]
      module
    have hxseg :
        x ∈ segment ℝ (D.vertexPlacement v) γ.vertices[1] := by
      have hxsmall :
          x ∈ segment ℝ (D.vertexPlacement v)
              (D.vertexPlacement v +
                R v • ((‖firstDirection v d‖)⁻¹ • firstDirection v d)) :=
        openSegment_subset_segment ℝ _ _ hx
      exact (convex_segment (𝕜 := ℝ) (D.vertexPlacement v) γ.vertices[1]).segment_subset
        (left_mem_segment ℝ (D.vertexPlacement v) γ.vertices[1]) hend_mem hxsmall
    have hx_arc : x ∈ γ.carrier := by
      rw [γ.carrier_eq]
      refine ⟨0, ?_, ?_⟩
      · simpa [γ] using hfirst
      · simpa [γ, hzero_vertex] using hxseg
    simpa [γ, A.dartArc_carrier d.1] using hx_arc
  · intro v d x hx
    dsimp [firstGerm, unitDirection] at hx
    have hcenter_closed :
        D.vertexPlacement v ∈ Metric.closedBall (D.vertexPlacement v) (R v) := by
      simp [le_of_lt (hR v)]
    have hunit_norm : ‖(‖firstDirection v d‖)⁻¹ • firstDirection v d‖ = 1 := by
      have hnorm_pos : 0 < ‖firstDirection v d‖ :=
        norm_pos_iff.mpr (firstDirection_ne_zero v d)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm_pos)]
      exact inv_mul_cancel₀ (ne_of_gt hnorm_pos)
    have hend_closed :
        D.vertexPlacement v + R v • ((‖firstDirection v d‖)⁻¹ • firstDirection v d) ∈
          Metric.closedBall (D.vertexPlacement v) (R v) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hsub :
          D.vertexPlacement v + R v • ((‖firstDirection v d‖)⁻¹ • firstDirection v d) -
              D.vertexPlacement v =
            R v • ((‖firstDirection v d‖)⁻¹ • firstDirection v d) := by
        module
      rw [hsub, norm_smul, hunit_norm, Real.norm_eq_abs, abs_of_pos (hR v)]
      simpa using (le_rfl : R v ≤ R v)
    have hend_ne :
        D.vertexPlacement v ≠
          D.vertexPlacement v + R v • ((‖firstDirection v d‖)⁻¹ • firstDirection v d) := by
      intro h
      have hunit_nonzero : ((‖firstDirection v d‖)⁻¹ • firstDirection v d) ≠ 0 := by
        intro hz
        rcases smul_eq_zero.mp hz with hscale | hdir
        · exact (inv_ne_zero (norm_ne_zero_iff.mpr (firstDirection_ne_zero v d))) hscale
        · exact firstDirection_ne_zero v d hdir
      have hscaled_ne :
          R v • ((‖firstDirection v d‖)⁻¹ • firstDirection v d) ≠ 0 :=
        smul_ne_zero (ne_of_gt (hR v)) hunit_nonzero
      have hzero :
          R v • ((‖firstDirection v d‖)⁻¹ • firstDirection v d) = 0 := by
        have h' :
            D.vertexPlacement v + R v • ((‖firstDirection v d‖)⁻¹ • firstDirection v d) =
              D.vertexPlacement v + (0 : EuclideanSpace ℝ (Fin 2)) := by
          simpa using h.symm
        exact add_left_cancel h'
      exact hscaled_ne hzero
    exact openSegment_subset_ball_of_ne hcenter_closed hend_closed hend_ne hx
