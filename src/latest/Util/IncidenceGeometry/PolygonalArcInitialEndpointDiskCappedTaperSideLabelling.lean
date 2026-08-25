import Util.IncidenceGeometry.PolygonalArcEndpointDiskCappedTaperChartTransport
import Util.IncidenceGeometry.PolygonalArcCollarCompatibleOrientedTubeData

open Set
open Classical
noncomputable section


lemma PolygonalArcInitialEndpointDiskCappedTaperSideLabelling
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (j : ℕ) (hj : j + 1 < γ.vertices.length) :
    let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
    let d : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1] - γ.vertices[j]
    let K : ℝ := compatibleTubes.initialConeBound j hj
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => γ.vertices[j] + z 0 • d + z 1 • PlanarRot90 d
    let a : ℝ :=
      controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
        dist γ.vertices[j] γ.vertices[j + 1]
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < K * z 0}
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧
        z 1 < K * z 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < 0}
    let G : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
    0 < a ∧
      IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
      IsConnected L ∧ IsConnected R ∧
      IsConnected (chart '' L) ∧ IsConnected (chart '' R) ∧
      Disjoint L R ∧ Disjoint (chart '' L) (chart '' R) ∧
      (0 : EuclideanSpace ℝ (Fin 2)) ∉ C ∧ G ⊆ C ∧ C \ G = L ∪ R ∧
      (∀ z : EuclideanSpace ℝ (Fin 2),
        z 0 ^ 2 + z 1 ^ 2 < a ^ 2 →
          chart z ∈ Metric.ball γ.vertices[j]
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩)) ∧
      chart '' C ⊆ Metric.ball γ.vertices[j]
        (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩) ∧
      γ.vertices[j] ∉ chart '' C ∧
      (∀ {t : ℝ}, 0 < t →
        chart (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠
          γ.vertices[j]) ∧
      ((AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Ioo (0 : ℝ) a ⊆
        chart '' G) ∧
      chart '' C \ chart '' G = chart '' L ∪ chart '' R ∧
      sep.leftHalf j hj ∩ chart '' C ⊆ chart '' L ∧
      sep.rightHalf j hj ∩ chart '' C ⊆ chart '' R := by
  intro sep d K chart a C L R G
  have hdist_pos : 0 < dist γ.vertices[j] γ.vertices[j + 1] := by
    have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
    have hleft := controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
    have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
    nlinarith
  have hp : γ.vertices[j + 1] ≠ γ.vertices[j] := by
    exact (dist_pos.mp hdist_pos).symm
  have hK : 0 < K := by
    dsimp [K]
    exact compatibleTubes.initialConeBound_pos j hj
  have htransport :=
    PolygonalArcEndpointDiskCappedTaperChartTransport
      (p0 := γ.vertices[j]) (p1 := γ.vertices[j + 1])
      (r := controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩) (K := K)
      hp (controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩) hK
  have htransport' :
      0 < a ∧
        IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
        IsConnected L ∧ IsConnected R ∧
        IsConnected (chart '' L) ∧ IsConnected (chart '' R) ∧
        Disjoint L R ∧ Disjoint (chart '' L) (chart '' R) ∧
        (0 : EuclideanSpace ℝ (Fin 2)) ∉ C ∧ G ⊆ C ∧ C \ G = L ∪ R ∧
        (∀ z : EuclideanSpace ℝ (Fin 2),
          z 0 ^ 2 + z 1 ^ 2 < a ^ 2 →
            chart z ∈
              Metric.ball γ.vertices[j]
                (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩)) ∧
        chart '' C ⊆
          Metric.ball γ.vertices[j]
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩) ∧
        γ.vertices[j] ∉ chart '' C ∧
        (∀ {t : ℝ}, 0 < t →
          chart (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠
            γ.vertices[j]) ∧
        ((AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Ioo (0 : ℝ) a ⊆
          chart '' G) ∧
        chart '' C \ chart '' G = chart '' L ∪ chart '' R := by
    simpa [d, chart, a, C, L, R, G] using htransport
  have hd : d ≠ 0 := by
    dsimp [d]
    exact sub_ne_zero.mpr hp
  have hchart_inj : Function.Injective chart := by
    intro z w hzw
    have hrep :
        (0 : EuclideanSpace ℝ (Fin 2)) =
          (z 0 - w 0) • d + (z 1 - w 1) • PlanarRot90 d := by
      have hzero : chart z - chart w = (0 : EuclideanSpace ℝ (Fin 2)) :=
        sub_eq_zero.mpr hzw
      have hdiff :
          chart z - chart w =
            (z 0 - w 0) • d + (z 1 - w 1) • PlanarRot90 d := by
        apply PiLp.ext
        intro k
        fin_cases k <;> simp [chart] <;> ring
      rw [← hdiff]
      exact hzero.symm
    have hcoeff :=
      PlanarRot90CoefficientUniqueness (d := d)
        (v := (0 : EuclideanSpace ℝ (Fin 2))) hd hrep
    have hz0 : z 0 = w 0 := by
      have h : z 0 - w 0 = 0 := by
        simpa using hcoeff.1
      linarith
    have hz1 : z 1 = w 1 := by
      have h : z 1 - w 1 = 0 := by
        simpa using hcoeff.2
      linarith
    apply PiLp.ext
    intro k
    fin_cases k
    · exact hz0
    · exact hz1
  have hleft_subset : sep.leftHalf j hj ∩ chart '' C ⊆ chart '' L := by
    rintro x ⟨hxLeft, hxC⟩
    rw [sep.leftHalf_eq j hj] at hxLeft
    rcases hxLeft with ⟨t, ht, s, hs, hx_eq⟩
    let z : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else s)
    have hx_chart : x = chart z := by
      rw [hx_eq]
      dsimp [chart, d, z]
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn j hj]
      apply PiLp.ext
      intro k
      fin_cases k <;> simp [PlanarRot90, AffineMap.lineMap_apply_module] <;> ring
    rcases hxC with ⟨w, hwC, hwx⟩
    have hwz : w = z := hchart_inj (by simpa [hx_chart] using hwx)
    have hzC : z ∈ C := by simpa [hwz] using hwC
    refine ⟨z, ?_, hx_chart.symm⟩
    dsimp [L]
    dsimp [C] at hzC
    have hKt_lower : K * sep.lowerParam j hj < K * t :=
      mul_lt_mul_of_pos_left ht.1 hK
    have hs_lt_Kt : s < K * t := by
      have hwidth := compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam j hj
      nlinarith [hs.2, hwidth, hKt_lower]
    have ht_pos : 0 < t := lt_trans (sep.lowerParam_pos j hj) ht.1
    rcases hzC with ⟨_, hzdisk, _, _⟩
    have hz0 : z 0 = t := by simp [z]
    have hz1 : z 1 = s := by simp [z]
    rw [hz0, hz1] at hzdisk
    exact ⟨by simpa [z] using ht_pos, hzdisk, by simpa [z] using hs.1,
      by simpa [z] using hs_lt_Kt⟩
  have hright_subset : sep.rightHalf j hj ∩ chart '' C ⊆ chart '' R := by
    rintro x ⟨hxRight, hxC⟩
    rw [sep.rightHalf_eq j hj] at hxRight
    rcases hxRight with ⟨t, ht, s, hs, hx_eq⟩
    let z : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else s)
    have hx_chart : x = chart z := by
      rw [hx_eq]
      dsimp [chart, d, z]
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn j hj]
      apply PiLp.ext
      intro k
      fin_cases k <;> simp [PlanarRot90, AffineMap.lineMap_apply_module] <;> ring
    rcases hxC with ⟨w, hwC, hwx⟩
    have hwz : w = z := hchart_inj (by simpa [hx_chart] using hwx)
    have hzC : z ∈ C := by simpa [hwz] using hwC
    refine ⟨z, ?_, hx_chart.symm⟩
    dsimp [R]
    dsimp [C] at hzC
    have hKt_lower : K * sep.lowerParam j hj < K * t :=
      mul_lt_mul_of_pos_left ht.1 hK
    have hneg_lt : -K * t < s := by
      have hwidth := compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam j hj
      nlinarith [hs.1, hwidth, hKt_lower]
    have ht_pos : 0 < t := lt_trans (sep.lowerParam_pos j hj) ht.1
    rcases hzC with ⟨_, hzdisk, _, _⟩
    have hz0 : z 0 = t := by simp [z]
    have hz1 : z 1 = s := by simp [z]
    rw [hz0, hz1] at hzdisk
    exact ⟨by simpa [z] using ht_pos, hzdisk, by simpa [z] using hneg_lt,
      by simpa [z] using hs.2⟩
  rcases htransport' with
    ⟨ha, hC_open, hL_open, hR_open, hL_conn, hR_conn, hchartL_conn,
      hchartR_conn, hLR_disj, hchartLR_disj, hzero_not_C, hG_sub_C, hsplit,
      hdisk_to_ball, hchartC_ball, hvertex_not_chartC, hcoord_omit,
      hgerm, himage_split⟩
  exact ⟨ha, hC_open, hL_open, hR_open, hL_conn, hR_conn, hchartL_conn,
    hchartR_conn, hLR_disj, hchartLR_disj, hzero_not_C, hG_sub_C, hsplit,
    hdisk_to_ball, hchartC_ball, hvertex_not_chartC, hcoord_omit, hgerm,
    himage_split, hleft_subset, hright_subset⟩

