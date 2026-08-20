import ErdosProblems.Erdos733.ST.PolygonalArcEndpointDiskCappedTaperChartTransport
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeData

open Set
open Classical
noncomputable section


-- [TABLET NODE: PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling]
lemma PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling
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
    let d : EuclideanSpace ℝ (Fin 2) := γ.vertices[j] - γ.vertices[j + 1]
    let K : ℝ := compatibleTubes.terminalConeBound j hj
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => γ.vertices[j + 1] + z 0 • d + z 1 • PlanarRot90 d
    let a : ℝ :=
      controlRadii.radius ⟨j + 1, hj⟩ /
        dist γ.vertices[j + 1] γ.vertices[j]
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
          chart z ∈
            Metric.ball γ.vertices[j + 1] (controlRadii.radius ⟨j + 1, hj⟩)) ∧
      chart '' C ⊆
        Metric.ball γ.vertices[j + 1] (controlRadii.radius ⟨j + 1, hj⟩) ∧
      γ.vertices[j + 1] ∉ chart '' C ∧
      (∀ {t : ℝ}, 0 < t →
        chart (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠
          γ.vertices[j + 1]) ∧
      ((AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
        chart '' G) ∧
      chart '' C \ chart '' G = chart '' L ∪ chart '' R ∧
      sep.leftHalf j hj ∩ chart '' C ⊆ chart '' R ∧
      sep.rightHalf j hj ∩ chart '' C ⊆ chart '' L := by
-- BODY
  intro sep d K chart a C L R G
  have hdist_pos : 0 < dist γ.vertices[j] γ.vertices[j + 1] := by
    have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
    have hleft := controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
    have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
    nlinarith
  have hp : γ.vertices[j] ≠ γ.vertices[j + 1] := by
    exact dist_pos.mp hdist_pos
  have hK : 0 < K := by
    dsimp [K]
    exact compatibleTubes.terminalConeBound_pos j hj
  have htransport :=
    PolygonalArcEndpointDiskCappedTaperChartTransport
      (p0 := γ.vertices[j + 1]) (p1 := γ.vertices[j])
      (r := controlRadii.radius ⟨j + 1, hj⟩) (K := K)
      hp (controlRadii.radius_pos ⟨j + 1, hj⟩) hK
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
              Metric.ball γ.vertices[j + 1] (controlRadii.radius ⟨j + 1, hj⟩)) ∧
        chart '' C ⊆
          Metric.ball γ.vertices[j + 1] (controlRadii.radius ⟨j + 1, hj⟩) ∧
        γ.vertices[j + 1] ∉ chart '' C ∧
        (∀ {t : ℝ}, 0 < t →
          chart (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠
            γ.vertices[j + 1]) ∧
        ((AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j]) '' Set.Ioo (0 : ℝ) a ⊆
          chart '' G) ∧
        chart '' C \ chart '' G = chart '' L ∪ chart '' R := by
    simpa [d, chart, a, C, L, R, G] using htransport
  rcases htransport' with
    ⟨ha, hC_open, hL_open, hR_open, hL_conn, hR_conn, hchartL_conn,
      hchartR_conn, hLR_disj, hchartLR_disj, hzero_not_C, hG_sub_C, hsplit,
      hdisk_to_ball, hchartC_ball, hvertex_not_chartC, hcoord_omit,
      hgerm_reversed, himage_split⟩
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
  have hgerm :
      ((AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
        chart '' G) := by
    rintro x ⟨t, ht, rfl⟩
    have ha_eq :
        a =
          controlRadii.radius ⟨j + 1, hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1] := by
      dsimp [a]
      rw [dist_comm]
    have hu : (1 - t) ∈ Set.Ioo (0 : ℝ) a := by
      constructor
      · linarith [ht.2]
      · rw [ha_eq]
        linarith [ht.1]
    have hline :
        AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j] (1 - t) =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t := by
      apply PiLp.ext
      intro k
      simp [AffineMap.lineMap_apply_module]
      ring
    have hx := hgerm_reversed ⟨1 - t, hu, rfl⟩
    simpa [hline] using hx
  have hleft_subset : sep.leftHalf j hj ∩ chart '' C ⊆ chart '' R := by
    rintro x ⟨hxLeft, hxC⟩
    rw [sep.leftHalf_eq j hj] at hxLeft
    rcases hxLeft with ⟨t, ht, s, hs, hx_eq⟩
    let z : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 1 - t else -s)
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
    have hupper_lt_one := sep.upperParam_lt_one j hj
    have ht_upper : t < sep.upperParam j hj := ht.2
    have ht_lt_one : t < 1 := lt_trans ht.2 hupper_lt_one
    have hterm_lt : K * (1 - sep.upperParam j hj) < K * (1 - t) :=
      mul_lt_mul_of_pos_left (by linarith : 1 - sep.upperParam j hj < 1 - t) hK
    have hneg_lt : -K * (1 - t) < -s := by
      have hs_upper : s < sep.halfWidth j hj := hs.2
      have hwidth := compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam j hj
      nlinarith [hs_upper, hwidth, hterm_lt]
    have hs_pos : 0 < s := hs.1
    rcases hzC with ⟨_, hzdisk, _, _⟩
    have hz0 : z 0 = 1 - t := by simp [z]
    have hz1 : z 1 = -s := by simp [z]
    rw [hz0, hz1] at hzdisk
    exact ⟨by simpa [z] using (by linarith : 0 < 1 - t), hzdisk,
      by simpa [z] using hneg_lt, by simpa [z] using (by linarith : -s < 0)⟩
  have hright_subset : sep.rightHalf j hj ∩ chart '' C ⊆ chart '' L := by
    rintro x ⟨hxRight, hxC⟩
    rw [sep.rightHalf_eq j hj] at hxRight
    rcases hxRight with ⟨t, ht, s, hs, hx_eq⟩
    let z : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 1 - t else -s)
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
    have hupper_lt_one := sep.upperParam_lt_one j hj
    have ht_upper : t < sep.upperParam j hj := ht.2
    have ht_lt_one : t < 1 := lt_trans ht.2 hupper_lt_one
    have hterm_lt : K * (1 - sep.upperParam j hj) < K * (1 - t) :=
      mul_lt_mul_of_pos_left (by linarith : 1 - sep.upperParam j hj < 1 - t) hK
    have hneg_s_lt : -s < K * (1 - t) := by
      have hs_lower : -sep.halfWidth j hj < s := hs.1
      have hwidth := compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam j hj
      nlinarith [hs_lower, hwidth, hterm_lt]
    have hs_neg : s < 0 := hs.2
    rcases hzC with ⟨_, hzdisk, _, _⟩
    have hz0 : z 0 = 1 - t := by simp [z]
    have hz1 : z 1 = -s := by simp [z]
    rw [hz0, hz1] at hzdisk
    exact ⟨by simpa [z] using (by linarith : 0 < 1 - t), hzdisk,
      by simpa [z] using (by linarith : 0 < -s), by simpa [z] using hneg_s_lt⟩
  exact ⟨ha, hC_open, hL_open, hR_open, hL_conn, hR_conn, hchartL_conn,
    hchartR_conn, hLR_disj, hchartLR_disj, hzero_not_C, hG_sub_C, hsplit,
    hdisk_to_ball, hchartC_ball, hvertex_not_chartC, hcoord_omit, hgerm,
    himage_split, hleft_subset, hright_subset⟩

