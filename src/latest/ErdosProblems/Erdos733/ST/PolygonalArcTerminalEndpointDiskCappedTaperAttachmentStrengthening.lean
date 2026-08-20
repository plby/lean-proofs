import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling

open Set
open Classical
noncomputable section


-- [TABLET NODE: PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening]
lemma PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
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
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧
        z 1 < K * z 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < 0}
    sep.leftHalf j hj ∩
        Metric.ball γ.vertices[j + 1] (controlRadii.radius ⟨j + 1, hj⟩) ⊆
      chart '' R ∧
    sep.rightHalf j hj ∩
        Metric.ball γ.vertices[j + 1] (controlRadii.radius ⟨j + 1, hj⟩) ⊆
      chart '' L := by
-- BODY
  intro sep d K chart a L R
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
  have hd : d ≠ 0 := by
    dsimp [d]
    exact sub_ne_zero.mpr hp
  have hdist_eq_normd : dist γ.vertices[j + 1] γ.vertices[j] = ‖d‖ := by
    rw [dist_eq_norm]
    dsimp [d]
    have hneg :
        γ.vertices[j + 1] - γ.vertices[j] =
          -(γ.vertices[j] - γ.vertices[j + 1]) := by
      abel
    rw [hneg, norm_neg]
  have hnormd_pos : 0 < ‖d‖ := by
    rw [← hdist_eq_normd]
    rwa [dist_comm]
  have hscale_sq :
      a ^ 2 * ‖d‖ ^ 2 =
        (controlRadii.radius ⟨j + 1, hj⟩) ^ 2 := by
    dsimp [a]
    rw [hdist_eq_normd]
    field_simp [ne_of_gt hnormd_pos]
  have hnorm_sq :
      ∀ z : EuclideanSpace ℝ (Fin 2),
        ‖z 0 • d + z 1 • PlanarRot90 d‖ ^ 2 =
          (z 0 ^ 2 + z 1 ^ 2) * ‖d‖ ^ 2 := by
    intro z
    have horth : inner ℝ (z 0 • d) (z 1 • PlanarRot90 d) = 0 := by
      rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
      ring
    have hpyth :
        ‖z 0 • d + z 1 • PlanarRot90 d‖ ^ 2 =
          ‖z 0 • d‖ ^ 2 + ‖z 1 • PlanarRot90 d‖ ^ 2 := by
      simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    rw [hpyth, norm_smul, norm_smul, PlanarRot90Norm]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  have ball_coord {z : EuclideanSpace ℝ (Fin 2)}
      (hz : chart z ∈
        Metric.ball γ.vertices[j + 1] (controlRadii.radius ⟨j + 1, hj⟩)) :
      z 0 ^ 2 + z 1 ^ 2 < a ^ 2 := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hsub :
        chart z - γ.vertices[j + 1] =
          z 0 • d + z 1 • PlanarRot90 d := by
      dsimp [chart]
      abel
    rw [hsub] at hz
    rw [← sq_lt_sq₀ (norm_nonneg _) (le_of_lt (controlRadii.radius_pos _))] at hz
    rw [hnorm_sq z] at hz
    have hpos_sq : 0 < ‖d‖ ^ 2 := sq_pos_of_pos hnormd_pos
    rw [← hscale_sq] at hz
    nlinarith
  constructor
  · rintro x ⟨hxLeft, hxBall⟩
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
    refine ⟨z, ?_, hx_chart.symm⟩
    dsimp [R]
    have hupper_lt_one := sep.upperParam_lt_one j hj
    have ht_lt_one : t < 1 := lt_trans ht.2 hupper_lt_one
    have hparam_lt : 1 - sep.upperParam j hj < 1 - t := by
      linarith [ht.2]
    have hterm_lt : K * (1 - sep.upperParam j hj) < K * (1 - t) :=
      mul_lt_mul_of_pos_left hparam_lt hK
    have hneg_lt : -K * (1 - t) < -s := by
      have hwidth := compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam j hj
      nlinarith [hs.2, hwidth, hterm_lt]
    have hzdisk : z 0 ^ 2 + z 1 ^ 2 < a ^ 2 := by
      apply ball_coord
      rwa [← hx_chart]
    exact ⟨by simpa [z] using (by linarith : 0 < 1 - t), hzdisk,
      by simpa [z] using hneg_lt, by simpa [z] using (by linarith [hs.1] : -s < 0)⟩
  · rintro x ⟨hxRight, hxBall⟩
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
    refine ⟨z, ?_, hx_chart.symm⟩
    dsimp [L]
    have hupper_lt_one := sep.upperParam_lt_one j hj
    have ht_lt_one : t < 1 := lt_trans ht.2 hupper_lt_one
    have hparam_lt : 1 - sep.upperParam j hj < 1 - t := by
      linarith [ht.2]
    have hterm_lt : K * (1 - sep.upperParam j hj) < K * (1 - t) :=
      mul_lt_mul_of_pos_left hparam_lt hK
    have hneg_s_lt : -s < K * (1 - t) := by
      have hwidth := compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam j hj
      nlinarith [hs.1, hwidth, hterm_lt]
    have hzdisk : z 0 ^ 2 + z 1 ^ 2 < a ^ 2 := by
      apply ball_coord
      rwa [← hx_chart]
    exact ⟨by simpa [z] using (by linarith : 0 < 1 - t), hzdisk,
      by simpa [z] using (by linarith [hs.2] : 0 < -s),
      by simpa [z] using hneg_s_lt⟩
