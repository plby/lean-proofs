import Util.IncidenceGeometry.PolygonalArcInteriorIncomingFramePositiveHalfTubeSectorRouting
import Util.IncidenceGeometry.PolygonalArcInteriorTwoRaySectorChartTransport

open Set
open Classical
noncomputable section


lemma PolygonalArcInteriorIncomingFrameSignedHalfTubeSectorRouting
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length)
    (c s : ℝ)
    (hrep : γ.vertices[j + 2] - γ.vertices[j + 1] =
      c • (γ.vertices[j] - γ.vertices[j + 1]) +
        s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]))
    (hpos : 0 < s ∨ s = 0 ∧ c < 0)
    (hCeq :
      let p : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1]
      let u : EuclideanSpace ℝ (Fin 2) := γ.vertices[j] - γ.vertices[j + 1]
      let rho : ℝ := controlRadii.radius ⟨j + 1, hj⟩
      let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
        fun z => p + z 0 • u + z 1 • PlanarRot90 u
      let C : Set (EuclideanSpace ℝ (Fin 2)) :=
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖u‖)
      chart '' C = Metric.ball p rho) :
    let sep :=
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
    let p : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1]
    let u : EuclideanSpace ℝ (Fin 2) := γ.vertices[j] - γ.vertices[j + 1]
    let rho : ℝ := controlRadii.radius ⟨j + 1, hj⟩
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • u + z 1 • PlanarRot90 u
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖u‖)
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
    sep.leftHalf j hj ∩ Metric.ball p rho ⊆ chart '' R ∧
      sep.leftHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' R ∧
      sep.rightHalf j hj ∩ Metric.ball p rho ⊆ chart '' L ∧
      sep.rightHalf (j + 1) hnext ∩ Metric.ball p rho ⊆ chart '' L := by
  intro sep p u rho chart C L R
  change chart '' C = Metric.ball p rho at hCeq
  have hpositive :
      sep.leftHalf j hj ∩ chart '' C ⊆ chart '' R ∧
        sep.leftHalf (j + 1) hnext ∩ chart '' C ⊆ chart '' R := by
    have hraw :=
      PolygonalArcInteriorIncomingFramePositiveHalfTubeSectorRouting
        γ controlRadii middleSegments forbiddenMargins compatibleTubes
        j hj hnext c s hrep hpos
    change
      sep.leftHalf j hj ∩ chart '' C ⊆ chart '' R ∧
        sep.leftHalf (j + 1) hnext ∩ chart '' C ⊆ chart '' R at hraw
    exact hraw
  have hdist_prev : 0 < dist γ.vertices[j] γ.vertices[j + 1] := by
    have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
    have hleft := controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
    have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
    nlinarith only [hsum, hleft, hright]
  have hdist_next : 0 < dist γ.vertices[j + 1] γ.vertices[j + 2] := by
    have hsum := controlRadii.adjacent_radii_sum_lt (j := j + 1) hnext
    have hleft := controlRadii.radius_pos ⟨j + 1, hj⟩
    have hright := controlRadii.radius_pos ⟨j + 2, hnext⟩
    nlinarith only [hsum, hleft, hright]
  have hu : u ≠ 0 := by
    dsimp [u]
    exact sub_ne_zero.mpr (dist_pos.mp hdist_prev)
  have hrep_u :
      γ.vertices[j + 2] - γ.vertices[j + 1] =
        c • u + s • PlanarRot90 u := by
    simpa [u] using hrep
  have hv :
      (γ.vertices[j + 2] - γ.vertices[j + 1]) ≠
        (0 : EuclideanSpace ℝ (Fin 2)) := by
    exact sub_ne_zero.mpr (dist_pos.mp hdist_next).symm
  have hchart_inj : Function.Injective chart := by
    intro z w hzw
    have hrep0 :
        (0 : EuclideanSpace ℝ (Fin 2)) =
          (z 0 - w 0) • u + (z 1 - w 1) • PlanarRot90 u := by
      have hzero : chart z - chart w = (0 : EuclideanSpace ℝ (Fin 2)) :=
        sub_eq_zero.mpr hzw
      have hdiff :
          chart z - chart w =
            (z 0 - w 0) • u + (z 1 - w 1) • PlanarRot90 u := by
        apply PiLp.ext
        intro k
        fin_cases k <;> simp [chart] <;> ring
      rw [← hdiff]
      exact hzero.symm
    have hcoeff :=
      PlanarRot90CoefficientUniqueness (d := u)
        (v := (0 : EuclideanSpace ℝ (Fin 2))) hu hrep0
    have hz0 : z 0 = w 0 := by
      have h : z 0 - w 0 = 0 := by
        simpa using hcoeff.1
      linarith only [h]
    have hz1 : z 1 = w 1 := by
      have h : z 1 - w 1 = 0 := by
        simpa using hcoeff.2
      linarith only [h]
    apply PiLp.ext
    intro k
    fin_cases k
    · exact hz0
    · exact hz1
  let a : ℝ := rho / ‖u‖
  have ha : 0 < a := by
    dsimp [a, rho]
    exact div_pos (controlRadii.radius_pos ⟨j + 1, hj⟩) (norm_pos_iff.mpr hu)
  have hC_sq :
      C =
        {q : EuclideanSpace ℝ (Fin 2) | q 0 ^ 2 + q 1 ^ 2 < a ^ 2} := by
    simpa [C, a] using (EuclideanSpace.ball_zero_eq (n := Fin 2) a ha.le)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨hxLeft, hxBall⟩
    exact hpositive.1 ⟨hxLeft, by rwa [hCeq]⟩
  · rintro x ⟨hxLeft, hxBall⟩
    exact hpositive.2 ⟨hxLeft, by rwa [hCeq]⟩
  · rintro x ⟨hxRight, hxBall⟩
    rw [sep.rightHalf_eq j hj] at hxRight
    rcases hxRight with ⟨t, ht, r, hr, hx_eq⟩
    let z : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then 1 - t else -r)
    have hx_chart : x = chart z := by
      rw [hx_eq]
      dsimp [chart, p, u, z]
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn j hj]
      apply PiLp.ext
      intro k
      fin_cases k <;> simp [PlanarRot90, AffineMap.lineMap_apply_module] <;> ring
    have hxCimage : x ∈ chart '' C := by
      rw [hCeq]
      exact hxBall
    rcases hxCimage with ⟨w, hwC, hwx⟩
    have hwz : w = z := hchart_inj (by simpa [hx_chart] using hwx)
    have hzC : z ∈ C := by simpa [hwz] using hwC
    have ht_lt_one : t < 1 := (ht.2).trans (sep.upperParam_lt_one j hj)
    have htau_pos : 0 < 1 - t := by linarith only [ht_lt_one]
    have hb_pos : 0 < -r := neg_pos.mpr hr.2
    refine ⟨z, ?_, hx_chart.symm⟩
    dsimp [L]
    refine ⟨hzC, by simpa [z] using hb_pos, ?_⟩
    have hcross_neg : c * (-r) - s * (1 - t) < 0 := by
      rcases hpos with hspos | ⟨hszero, hcneg⟩
      · by_contra hnot
        have hcross_nonneg : 0 ≤ c * (-r) - s * (1 - t) :=
          le_of_not_gt hnot
        have hc_pos : 0 < c := by
          by_contra hcnot
          have hc_nonpos : c ≤ 0 := le_of_not_gt hcnot
          nlinarith only [hcross_nonneg, hspos, htau_pos, hb_pos, hc_nonpos]
        let b0 : ℝ := s * (1 - t) / c
        have hb0_pos : 0 < b0 := by
          dsimp [b0]
          exact div_pos (mul_pos hspos htau_pos) hc_pos
        have hb0_le : b0 ≤ -r := by
          dsimp [b0]
          rw [div_le_iff₀ hc_pos]
          linarith only [hcross_nonneg]
        have hwidth :
            sep.halfWidth j hj <
              compatibleTubes.terminalConeBound j hj * (1 - sep.upperParam j hj) := by
          simpa [sep] using
            compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
              j hj
        have hcone_pos := compatibleTubes.terminalConeBound_pos j hj
        have hterm_lt :
            compatibleTubes.terminalConeBound j hj * (1 - sep.upperParam j hj) <
              compatibleTubes.terminalConeBound j hj * (1 - t) := by
          exact mul_lt_mul_of_pos_left (by linarith only [ht.2]) hcone_pos
        have hb_lt_width : -r < sep.halfWidth j hj := by
          linarith only [hr.1]
        have hb0_lt_cone :
            b0 < compatibleTubes.terminalConeBound j hj * (1 - t) :=
          lt_of_le_of_lt hb0_le (hb_lt_width.trans (hwidth.trans hterm_lt))
        let ycoord : EuclideanSpace ℝ (Fin 2) :=
          WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then 1 - t else b0)
        have hz_sq : (1 - t) ^ 2 + (-r) ^ 2 < a ^ 2 := by
          have hzC' := hzC
          rw [hC_sq] at hzC'
          simpa [z] using hzC'
        have hycoordC : ycoord ∈ C := by
          rw [hC_sq]
          dsimp [ycoord]
          have hb0_sq_le : b0 ^ 2 ≤ (-r) ^ 2 := by
            nlinarith only [hb0_pos, hb0_le]
          nlinarith only [hz_sq, hb0_sq_le]
        let lam : ℝ := (1 - t) / c
        have hlam_pos : 0 < lam := by
          dsimp [lam]
          exact div_pos htau_pos hc_pos
        have hy_chart_eq :
            chart ycoord = p + lam • (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
          dsimp [chart, ycoord, lam, b0]
          rw [hrep_u]
          apply PiLp.ext
          intro k
          fin_cases k <;> simp [PlanarRot90] <;>
            field_simp [ne_of_gt hc_pos] <;> ring_nf
        have hyBall :
            p + lam • (γ.vertices[j + 2] - γ.vertices[j + 1]) ∈
              Metric.ball p rho := by
          have : chart ycoord ∈ chart '' C := ⟨ycoord, hycoordC, rfl⟩
          rw [hCeq] at this
          simpa [hy_chart_eq] using this
        have hvnorm_pos :
            0 < ‖γ.vertices[j + 2] - γ.vertices[j + 1]‖ := norm_pos_iff.mpr hv
        have hrho_lt_vnorm :
            rho < ‖γ.vertices[j + 2] - γ.vertices[j + 1]‖ := by
          have hsum := controlRadii.adjacent_radii_sum_lt (j := j + 1) hnext
          have hnext_radius := controlRadii.radius_pos ⟨j + 2, hnext⟩
          have hdist_eq :
              dist γ.vertices[j + 1] γ.vertices[j + 2] =
                ‖γ.vertices[j + 2] - γ.vertices[j + 1]‖ := by
            rw [dist_eq_norm]
            have hneg :
                γ.vertices[j + 1] - γ.vertices[j + 2] =
                  -(γ.vertices[j + 2] - γ.vertices[j + 1]) := by
              abel
            rw [hneg, norm_neg]
          dsimp [rho] at *
          rw [hdist_eq] at hsum
          nlinarith only [hsum, hnext_radius]
        have hlam_le_one : lam ≤ 1 := by
          by_contra hnotle
          have hlam_gt : 1 < lam := lt_of_not_ge hnotle
          have hdist_expr :
              dist (p + lam • (γ.vertices[j + 2] - γ.vertices[j + 1])) p =
                lam * ‖γ.vertices[j + 2] - γ.vertices[j + 1]‖ := by
            rw [dist_eq_norm]
            have hsub :
                p + lam • (γ.vertices[j + 2] - γ.vertices[j + 1]) - p =
                  lam • (γ.vertices[j + 2] - γ.vertices[j + 1]) := by
              abel
            rw [hsub, norm_smul, Real.norm_eq_abs,
              abs_of_pos (lt_trans zero_lt_one hlam_gt)]
          rw [Metric.mem_ball, hdist_expr] at hyBall
          nlinarith only [hyBall, hrho_lt_vnorm, hlam_gt, hvnorm_pos]
        let y : EuclideanSpace ℝ (Fin 2) :=
          p + lam • (γ.vertices[j + 2] - γ.vertices[j + 1])
        have hy_next : y ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] := by
          rw [segment_eq_image_lineMap]
          refine ⟨lam, ⟨le_of_lt hlam_pos, hlam_le_one⟩, ?_⟩
          apply PiLp.ext
          intro k
          fin_cases k <;> simp [y, p, AffineMap.lineMap_apply_module] <;> ring
        have hy_cone :
            y ∈
              {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
                ∃ s : ℝ, s ≠ 0 ∧
                  |s| < compatibleTubes.terminalConeBound j hj * (1 - t) ∧
                    z =
                      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                        s • sep.normal j hj} := by
          refine ⟨t, ⟨(sep.lowerParam_pos j hj).trans ht.1, ht_lt_one⟩,
            -b0, neg_ne_zero.mpr (ne_of_gt hb0_pos), ?_, ?_⟩
          · simpa [abs_neg, abs_of_pos hb0_pos] using hb0_lt_cone
          · have hnormal : sep.normal j hj = -PlanarRot90 u := by
              rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn j hj]
              dsimp [u]
              apply PiLp.ext
              intro k
              fin_cases k <;> simp [PlanarRot90]
            have hy_eq : y = chart ycoord := by
              rw [hy_chart_eq]
            rw [hy_eq]
            dsimp [chart, ycoord, p, u]
            rw [hnormal]
            apply PiLp.ext
            intro k
            fin_cases k <;> simp [AffineMap.lineMap_apply_module, PlanarRot90, u] <;>
              ring_nf
        exact
          (Set.disjoint_left.mp
            (compatibleTubes.terminal_signed_cone_disjoint_next_segment
              j hj hnext) hy_cone) hy_next
      · simpa only [hszero, zero_mul, sub_zero] using
          (mul_neg_of_neg_of_pos hcneg hb_pos)
    have hz0 : z 0 = 1 - t := by simp [z]
    have hz1 : z 1 = -r := by simp [z]
    rw [hz0, hz1]
    exact hcross_neg
  · rintro x ⟨hxRight, hxBall⟩
    rw [sep.rightHalf_eq (j + 1) hnext] at hxRight
    rcases hxRight with ⟨t, ht, r, hr, hx_eq⟩
    let v : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 2] - γ.vertices[j + 1]
    let z : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun k : Fin 2 =>
        if k = 0 then t * c - r * s else t * s + r * c)
    have hrot_v : PlanarRot90 v = (-s) • u + c • PlanarRot90 u := by
      rw [show v = c • u + s • PlanarRot90 u by simpa [v] using hrep_u]
      exact PlanarRot90LinearCombination u c s
    have hline_next :
        AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 1 + 1] t =
          p + t • v := by
      have hidx : j + 1 + 1 = j + 2 := by omega
      apply PiLp.ext
      intro k
      fin_cases k <;> simp [p, v, hidx, AffineMap.lineMap_apply_module] <;> ring
    have hnormal_next : sep.normal (j + 1) hnext = PlanarRot90 v := by
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn (j + 1) hnext]
      have hidx : j + 1 + 1 = j + 2 := by omega
      apply PiLp.ext
      intro k
      fin_cases k <;> simp [PlanarRot90, v, hidx]
    have hx_chart : x = chart z := by
      calc
        x = AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 1 + 1] t +
            r • sep.normal (j + 1) hnext := hx_eq
        _ = p + t • v + r • PlanarRot90 v := by rw [hline_next, hnormal_next]
        _ = chart z := by
          dsimp [chart, z]
          rw [hrot_v, show v = c • u + s • PlanarRot90 u by simpa [v] using hrep_u]
          apply PiLp.ext
          intro k
          fin_cases k <;> simp [PlanarRot90] <;> ring
    have hxCimage : x ∈ chart '' C := by
      rw [hCeq]
      exact hxBall
    rcases hxCimage with ⟨w, hwC, hwx⟩
    have hwz : w = z := hchart_inj (by simpa [hx_chart] using hwx)
    have hzC : z ∈ C := by simpa [hwz] using hwC
    have ht_pos : 0 < t := (sep.lowerParam_pos (j + 1) hnext).trans ht.1
    have ht_lt_one : t < 1 := (ht.2).trans (sep.upperParam_lt_one (j + 1) hnext)
    have hD_pos : 0 < c ^ 2 + s ^ 2 := by
      rcases hpos with hspos | ⟨hszero, hcneg⟩
      · nlinarith only [hspos]
      · nlinarith only [hcneg]
    refine ⟨z, ?_, hx_chart.symm⟩
    dsimp [L]
    refine ⟨hzC, ?_, ?_⟩
    · have hz1_pos : 0 < t * s + r * c := by
        rcases hpos with hspos | ⟨hszero, hcneg⟩
        · by_contra hnot
          have hnonpos : t * s + r * c ≤ 0 := le_of_not_gt hnot
          have hc_pos : 0 < c := by
            by_contra hcnot
            have hc_nonpos : c ≤ 0 := le_of_not_gt hcnot
            nlinarith only [hnonpos, ht_pos, hspos, hr.2, hc_nonpos]
          let b0 : ℝ := t * s / c
          have hb0_pos : 0 < b0 := by
            dsimp [b0]
            exact div_pos (mul_pos ht_pos hspos) hc_pos
          have hb0_le : b0 ≤ -r := by
            dsimp [b0]
            rw [div_le_iff₀ hc_pos]
            nlinarith only [hnonpos]
          have hwidth :
              sep.halfWidth (j + 1) hnext <
                compatibleTubes.initialConeBound (j + 1) hnext *
                  sep.lowerParam (j + 1) hnext := by
            simpa [sep] using
              compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam
                (j + 1) hnext
          have hcone_pos := compatibleTubes.initialConeBound_pos (j + 1) hnext
          have hinit_lt :
              compatibleTubes.initialConeBound (j + 1) hnext *
                  sep.lowerParam (j + 1) hnext <
                compatibleTubes.initialConeBound (j + 1) hnext * t := by
            exact mul_lt_mul_of_pos_left ht.1 hcone_pos
          have hb_lt_width : -r < sep.halfWidth (j + 1) hnext := by
            linarith only [hr.1]
          have hb0_lt_cone :
              b0 < compatibleTubes.initialConeBound (j + 1) hnext * t :=
            lt_of_le_of_lt hb0_le (hb_lt_width.trans (hwidth.trans hinit_lt))
          let ycoord : EuclideanSpace ℝ (Fin 2) :=
            WithLp.toLp 2 (fun k : Fin 2 =>
              if k = 0 then t * c + b0 * s else 0)
          have hz_sq : (t * c - r * s) ^ 2 + (t * s + r * c) ^ 2 < a ^ 2 := by
            have hzC' := hzC
            rw [hC_sq] at hzC'
            simpa [z] using hzC'
          have hy_sq_le :
              (t * c + b0 * s) ^ 2 ≤
                (t * c - r * s) ^ 2 + (t * s + r * c) ^ 2 := by
            have hb0_sq_le : b0 ^ 2 ≤ (-r) ^ 2 := by
              nlinarith only [hb0_pos, hb0_le]
            have hz_formula :
                (t * c - r * s) ^ 2 + (t * s + r * c) ^ 2 =
                  (t ^ 2 + r ^ 2) * (c ^ 2 + s ^ 2) := by
              ring
            have hy_formula :
                (t * c + b0 * s) ^ 2 =
                  (t ^ 2 + b0 ^ 2) * (c ^ 2 + s ^ 2) := by
              dsimp [b0]
              field_simp [ne_of_gt hc_pos]
            rw [hz_formula, hy_formula]
            nlinarith only [hb0_sq_le, hD_pos]
          have hycoordC : ycoord ∈ C := by
            rw [hC_sq]
            dsimp [ycoord]
            nlinarith only [hz_sq, hy_sq_le]
          let lam : ℝ := t * (c ^ 2 + s ^ 2) / c
          have hlam_pos : 0 < lam := by
            dsimp [lam]
            exact div_pos (mul_pos ht_pos hD_pos) hc_pos
          have hcoord_lam : t * c + b0 * s = lam := by
            dsimp [lam, b0]
            field_simp [ne_of_gt hc_pos]
          have hy_chart_eq :
              chart ycoord = p + lam • u := by
            dsimp [chart, ycoord]
            rw [hcoord_lam]
            simp
          have hyBall : p + lam • u ∈ Metric.ball p rho := by
            have : chart ycoord ∈ chart '' C := ⟨ycoord, hycoordC, rfl⟩
            rw [hCeq] at this
            simpa [hy_chart_eq] using this
          have hrho_lt_unorm : rho < ‖u‖ := by
            have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
            have hprev_radius := controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
            have hdist_eq : dist γ.vertices[j] γ.vertices[j + 1] = ‖u‖ := by
              dsimp [u]
              rw [dist_eq_norm]
            dsimp [rho] at *
            rw [hdist_eq] at hsum
            nlinarith only [hsum, hprev_radius]
          have hlam_le_one : lam ≤ 1 := by
            by_contra hnotle
            have hlam_gt : 1 < lam := lt_of_not_ge hnotle
            have hdist_expr : dist (p + lam • u) p = lam * ‖u‖ := by
              rw [dist_eq_norm]
              have hsub : p + lam • u - p = lam • u := by abel
              rw [hsub, norm_smul, Real.norm_eq_abs,
                abs_of_pos (lt_trans zero_lt_one hlam_gt)]
            rw [Metric.mem_ball, hdist_expr] at hyBall
            nlinarith only [hyBall, hrho_lt_unorm, hlam_gt, norm_pos_iff.mpr hu]
          let y : EuclideanSpace ℝ (Fin 2) := p + lam • u
          have hy_prev : y ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
            rw [segment_eq_image_lineMap]
            refine ⟨1 - lam,
              ⟨by linarith only [hlam_le_one], by linarith only [hlam_pos]⟩, ?_⟩
            apply PiLp.ext
            intro k
            fin_cases k <;> simp [y, p, u, AffineMap.lineMap_apply_module] <;> ring
          have hy_cone :
              y ∈
                {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
                  ∃ s : ℝ, s ≠ 0 ∧
                    |s| < compatibleTubes.initialConeBound (j + 1) hnext * t ∧
                      z =
                        AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                          s • sep.normal (j + 1) hnext} := by
            refine ⟨t, ⟨ht_pos, ht_lt_one⟩, -b0,
              neg_ne_zero.mpr (ne_of_gt hb0_pos), ?_, ?_⟩
            · simpa [abs_neg, abs_of_pos hb0_pos] using hb0_lt_cone
            · have htarget :
                  y = p + t • v + (-b0) • PlanarRot90 v := by
                dsimp [y, lam, b0]
                rw [show v = c • u + s • PlanarRot90 u by simpa [v] using hrep_u]
                rw [PlanarRot90LinearCombination u c s]
                apply PiLp.ext
                intro k
                fin_cases k <;> simp [PlanarRot90] <;>
                  field_simp [ne_of_gt hc_pos] <;> ring_nf
              calc
                y = p + t • v + (-b0) • PlanarRot90 v := htarget
                _ =
                    AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                      (-b0) • sep.normal (j + 1) hnext := by
                  rw [hline_next, hnormal_next]
          exact
            (Set.disjoint_left.mp
              (compatibleTubes.initial_signed_cone_disjoint_previous_segment
                (j + 1) hnext (Nat.succ_pos j)) hy_cone) hy_prev
        · rw [hszero]
          have hr_mul_c : 0 < r * c := mul_pos_of_neg_of_neg hr.2 hcneg
          linarith only [hr_mul_c]
      simpa [z] using hz1_pos
    · have hcross : c * z 1 - s * z 0 = r * (c ^ 2 + s ^ 2) := by
        simp [z]
        ring
      rw [hcross]
      exact mul_neg_of_neg_of_pos hr.2 hD_pos
