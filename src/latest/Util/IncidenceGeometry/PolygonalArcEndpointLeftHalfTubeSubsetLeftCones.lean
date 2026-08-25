import Mathlib.Tactic
import Util.IncidenceGeometry.PolygonalArcCollarCompatibleOrientedTubeData
import Util.IncidenceGeometry.PolygonalArcEndpointIsolation
import Util.IncidenceGeometry.PolygonalArcInitialEndpointLeftCone
import Util.IncidenceGeometry.PolygonalArcInitialEndpointSegmentLength
import Util.IncidenceGeometry.PlanarRot90
import Util.IncidenceGeometry.PlanarRot90Norm
import Util.IncidenceGeometry.PlanarRot90Orthogonal
import Util.IncidenceGeometry.PolygonalArcReverse
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointLeftCone
import Util.IncidenceGeometry.PolygonalArcTerminalEndpointSegmentLength

open Classical
noncomputable section

lemma PolygonalArcEndpointLeftHalfTubeSubsetLeftCones (γ : PolygonalArc)
    {η : ℝ} (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (r₀ r₁ K₀ K₁ : ℝ) :
    PolygonalArcEndpointIsolation γ r₀ r₁ →
      0 < K₀ →
        0 < K₁ →
          ∀ (hfirst : 0 + 1 < γ.vertices.length)
            (hlast : (γ.vertices.length - 2) + 1 < γ.vertices.length),
            compatibleTubes.initialConeBound 0 hfirst < K₀ →
              compatibleTubes.terminalConeBound (γ.vertices.length - 2) hlast <
                K₁ →
                (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
                    0 hfirst ∩ Metric.ball γ.source r₀ ⊆
                  PolygonalArcInitialEndpointLeftCone γ r₀ K₀) ∧
                  (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
                      (γ.vertices.length - 2) hlast ∩
                        Metric.ball γ.target r₁ ⊆
                    PolygonalArcTerminalEndpointLeftCone γ r₁ K₁) ∧
                    (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
                        0 hfirst ∩ Metric.ball γ.source r₀ ⊆
                      PolygonalArcTerminalEndpointLeftCone
                        (PolygonalArcReverse γ) r₀ K₀) ∧
                      (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
                          (γ.vertices.length - 2) hlast ∩
                            Metric.ball γ.target r₁ ⊆
                        PolygonalArcInitialEndpointLeftCone
                          (PolygonalArcReverse γ) r₁ K₁) := by
  intro hIso hK₀ hK₁ hfirst hlast hKinit_lt hKterm_lt
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  have hsourceIdx : 0 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  have hsource_vertex : γ.vertices[0] = γ.source := by
    have hget : γ.vertices[0]? = some γ.vertices[0] :=
      List.getElem?_eq_getElem hsourceIdx
    rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
    exact Option.some.inj hget.symm
  let jlast : ℕ := γ.vertices.length - 2
  let itarget : ℕ := γ.vertices.length - 1
  have htargetIdx : itarget < γ.vertices.length := by
    have hlen := γ.length_ge_two
    dsimp [itarget]
    omega
  have hlast_eq : jlast = γ.vertices.length - 2 := rfl
  have hlast' : jlast + 1 < γ.vertices.length := by
    simpa [jlast] using hlast
  have hlast_succ : jlast + 1 = itarget := by
    have hlen := γ.length_ge_two
    dsimp [jlast, itarget]
    omega
  have htarget_vertex : γ.vertices[itarget] = γ.target := by
    have htargetIdx' : γ.vertices.length - 1 < γ.vertices.length := by
      simpa [itarget] using htargetIdx
    have hget :
        γ.vertices[γ.vertices.length - 1]? =
          some γ.vertices[γ.vertices.length - 1] :=
      List.getElem?_eq_getElem htargetIdx'
    rw [← List.getLast?_eq_getElem?, γ.target_eq_last] at hget
    simpa [itarget] using Option.some.inj hget.symm
  have htarget_last_vertex : γ.vertices[jlast + 1] = γ.target := by
    simpa [hlast_succ] using htarget_vertex
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro z ⟨hzLeft, hzBall⟩
    rw [sep.leftHalf_eq 0 hfirst] at hzLeft
    rcases hzLeft with ⟨t, ht, s, hs, hz_eq⟩
    let d : EuclideanSpace ℝ (Fin 2) := γ.vertices[1] - γ.source
    let q : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then t else s)
    have hdist_pos : 0 < dist γ.source γ.vertices[1] := by
      have hlen_pos :
          0 < PolygonalArcInitialEndpointSegmentLength γ :=
        lt_trans hIso.source_pos hIso.source_lt_initial_length
      simpa [PolygonalArcInitialEndpointSegmentLength] using hlen_pos
    have hdist_eq_normd : dist γ.source γ.vertices[1] = ‖d‖ := by
      rw [dist_eq_norm]
      dsimp [d]
      have hneg : γ.source - γ.vertices[1] =
          -(γ.vertices[1] - γ.source) := by
        abel
      rw [hneg, norm_neg]
    have hnormd_pos : 0 < ‖d‖ := by
      simpa [← hdist_eq_normd] using hdist_pos
    have hnorm_sq :
        ‖t • d + s • PlanarRot90 d‖ ^ 2 =
          (t ^ 2 + s ^ 2) * ‖d‖ ^ 2 := by
      have horth : inner ℝ (t • d) (s • PlanarRot90 d) = 0 := by
        rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
        ring
      have hpyth :
          ‖t • d + s • PlanarRot90 d‖ ^ 2 =
            ‖t • d‖ ^ 2 + ‖s • PlanarRot90 d‖ ^ 2 := by
        simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      rw [hpyth, norm_smul, norm_smul, PlanarRot90Norm]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have hz_chart :
        z = γ.source + t • d + s • PlanarRot90 d := by
      rw [hz_eq]
      dsimp [d]
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn 0 hfirst]
      rw [hsource_vertex]
      apply PiLp.ext
      intro k
      fin_cases k <;>
        simp [PlanarRot90, AffineMap.lineMap_apply_module] <;>
        ring
    have hzBallNorm : ‖z - γ.source‖ < r₀ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzBall
    have hzBallSq : ‖z - γ.source‖ ^ 2 < r₀ ^ 2 := by
      have hsq := hzBallNorm
      rw [← sq_lt_sq₀ (norm_nonneg _) (le_of_lt hIso.source_pos)] at hsq
      exact hsq
    have hsub : z - γ.source = t • d + s • PlanarRot90 d := by
      rw [hz_chart]
      abel
    have hdisk : t ^ 2 + s ^ 2 <
        (r₀ / dist γ.source γ.vertices[1]) ^ 2 := by
      have hscale :
          (r₀ / dist γ.source γ.vertices[1]) ^ 2 * ‖d‖ ^ 2 = r₀ ^ 2 := by
        rw [hdist_eq_normd]
        field_simp [ne_of_gt hnormd_pos]
      rw [hsub, hnorm_sq] at hzBallSq
      rw [← hscale] at hzBallSq
      have hpos_sq : 0 < ‖d‖ ^ 2 := sq_pos_of_pos hnormd_pos
      exact lt_of_mul_lt_mul_right hzBallSq (le_of_lt hpos_sq)
    have ht_pos : 0 < t := lt_trans (sep.lowerParam_pos 0 hfirst) ht.1
    have hprod_le :
        compatibleTubes.initialConeBound 0 hfirst *
            sep.lowerParam 0 hfirst ≤
          K₀ * t := by
      exact mul_le_mul (le_of_lt hKinit_lt) (le_of_lt ht.1)
        (le_of_lt (sep.lowerParam_pos 0 hfirst)) (le_of_lt hK₀)
    have hwidth_lt_Kt :
        sep.halfWidth 0 hfirst < K₀ * t :=
      lt_of_lt_of_le
        (compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam 0 hfirst)
        hprod_le
    have hs_upper : s < K₀ * t := lt_trans hs.2 hwidth_lt_Kt
    rw [PolygonalArcInitialEndpointLeftCone]
    refine ⟨q, ?_, ?_⟩
    · dsimp [q]
      exact ⟨by simpa using ht_pos, by simpa using hdisk,
        by simpa using hs.1, by simpa using hs_upper⟩
    · simpa [q, d, hsource_vertex] using hz_chart.symm
  · rintro z ⟨hzLeft, hzBall⟩
    rw [show
        sep.leftHalf (γ.vertices.length - 2) hlast =
          sep.leftHalf jlast hlast' by
      rfl] at hzLeft
    rw [sep.leftHalf_eq jlast hlast'] at hzLeft
    rcases hzLeft with ⟨t, ht, s, hs, hz_eq⟩
    let d : EuclideanSpace ℝ (Fin 2) := γ.vertices[jlast] - γ.target
    let q : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then 1 - t else -s)
    have hdist_pos : 0 < dist γ.target γ.vertices[jlast] := by
      have hlen_pos :
          0 < PolygonalArcTerminalEndpointSegmentLength γ :=
        lt_trans hIso.target_pos hIso.target_lt_terminal_length
      simpa [PolygonalArcTerminalEndpointSegmentLength, jlast] using hlen_pos
    have hdist_eq_normd : dist γ.target γ.vertices[jlast] = ‖d‖ := by
      rw [dist_eq_norm]
      dsimp [d]
      have hneg : γ.target - γ.vertices[jlast] =
          -(γ.vertices[jlast] - γ.target) := by
        abel
      rw [hneg, norm_neg]
    have hnormd_pos : 0 < ‖d‖ := by
      simpa [← hdist_eq_normd] using hdist_pos
    have hnorm_sq :
        ‖(1 - t) • d + (-s) • PlanarRot90 d‖ ^ 2 =
          ((1 - t) ^ 2 + (-s) ^ 2) * ‖d‖ ^ 2 := by
      have horth :
          inner ℝ ((1 - t) • d) ((-s) • PlanarRot90 d) = 0 := by
        rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
        ring
      have hpyth :
          ‖(1 - t) • d + (-s) • PlanarRot90 d‖ ^ 2 =
            ‖(1 - t) • d‖ ^ 2 + ‖(-s) • PlanarRot90 d‖ ^ 2 := by
        simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      rw [hpyth, norm_smul, norm_smul, PlanarRot90Norm]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have hz_chart :
        z = γ.target + (1 - t) • d + (-s) • PlanarRot90 d := by
      rw [hz_eq]
      dsimp [d]
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn jlast hlast']
      rw [htarget_last_vertex]
      apply PiLp.ext
      intro k
      fin_cases k <;>
        simp [PlanarRot90, AffineMap.lineMap_apply_module] <;>
        ring
    have hzBallNorm : ‖z - γ.target‖ < r₁ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzBall
    have hzBallSq : ‖z - γ.target‖ ^ 2 < r₁ ^ 2 := by
      have hsq := hzBallNorm
      rw [← sq_lt_sq₀ (norm_nonneg _) (le_of_lt hIso.target_pos)] at hsq
      exact hsq
    have hsub :
        z - γ.target = (1 - t) • d + (-s) • PlanarRot90 d := by
      rw [hz_chart]
      abel
    have hdisk : (1 - t) ^ 2 + (-s) ^ 2 <
        (r₁ / dist γ.target γ.vertices[jlast]) ^ 2 := by
      have hscale :
          (r₁ / dist γ.target γ.vertices[jlast]) ^ 2 * ‖d‖ ^ 2 = r₁ ^ 2 := by
        rw [hdist_eq_normd]
        field_simp [ne_of_gt hnormd_pos]
      rw [hsub, hnorm_sq] at hzBallSq
      rw [← hscale] at hzBallSq
      have hpos_sq : 0 < ‖d‖ ^ 2 := sq_pos_of_pos hnormd_pos
      exact lt_of_mul_lt_mul_right hzBallSq (le_of_lt hpos_sq)
    have ht_lt_one : t < 1 :=
      lt_trans ht.2 (sep.upperParam_lt_one jlast hlast')
    have hone_sub_pos : 0 < 1 - t := sub_pos.mpr ht_lt_one
    have hparam_le : 1 - sep.upperParam jlast hlast' ≤ 1 - t := by
      exact sub_le_sub_left (le_of_lt ht.2) 1
    have hprod_le :
        compatibleTubes.terminalConeBound jlast hlast' *
            (1 - sep.upperParam jlast hlast') ≤
          K₁ * (1 - t) := by
      have hKterm_lt' :
          compatibleTubes.terminalConeBound jlast hlast' < K₁ := by
        simpa [jlast] using hKterm_lt
      exact mul_le_mul (le_of_lt hKterm_lt') hparam_le
        (by
          have hright :
              0 < 1 - sep.upperParam jlast hlast' := by
            linarith [sep.upperParam_lt_one jlast hlast']
          exact le_of_lt hright)
        (le_of_lt hK₁)
    have hwidth_lt_Kt :
        sep.halfWidth jlast hlast' < K₁ * (1 - t) :=
      lt_of_lt_of_le
        (compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
          jlast hlast')
        hprod_le
    have hs_lower : -K₁ * (1 - t) < -s := by
      linarith [hs.2, hwidth_lt_Kt]
    have hs_upper : -s < 0 := by
      linarith [hs.1]
    rw [PolygonalArcTerminalEndpointLeftCone]
    refine ⟨q, ?_, ?_⟩
    · dsimp [q]
      exact ⟨by simpa using hone_sub_pos, by simpa using hdisk,
        by simpa using hs_lower, by simpa using hs_upper⟩
    · simpa [q, d, jlast, hlast_succ, htarget_last_vertex] using hz_chart.symm
  · rintro z ⟨hzRight, hzBall⟩
    rw [sep.rightHalf_eq 0 hfirst] at hzRight
    rcases hzRight with ⟨t, ht, s, hs, hz_eq⟩
    let d : EuclideanSpace ℝ (Fin 2) := γ.vertices[1] - γ.source
    let q : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then t else s)
    have hdist_pos : 0 < dist γ.source γ.vertices[1] := by
      have hlen_pos :
          0 < PolygonalArcInitialEndpointSegmentLength γ :=
        lt_trans hIso.source_pos hIso.source_lt_initial_length
      simpa [PolygonalArcInitialEndpointSegmentLength] using hlen_pos
    have hdist_eq_normd : dist γ.source γ.vertices[1] = ‖d‖ := by
      rw [dist_eq_norm]
      dsimp [d]
      have hneg : γ.source - γ.vertices[1] =
          -(γ.vertices[1] - γ.source) := by
        abel
      rw [hneg, norm_neg]
    have hnormd_pos : 0 < ‖d‖ := by
      simpa [← hdist_eq_normd] using hdist_pos
    have hnorm_sq :
        ‖t • d + s • PlanarRot90 d‖ ^ 2 =
          (t ^ 2 + s ^ 2) * ‖d‖ ^ 2 := by
      have horth : inner ℝ (t • d) (s • PlanarRot90 d) = 0 := by
        rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
        ring
      have hpyth :
          ‖t • d + s • PlanarRot90 d‖ ^ 2 =
            ‖t • d‖ ^ 2 + ‖s • PlanarRot90 d‖ ^ 2 := by
        simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      rw [hpyth, norm_smul, norm_smul, PlanarRot90Norm]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have hz_chart :
        z = γ.source + t • d + s • PlanarRot90 d := by
      rw [hz_eq]
      dsimp [d]
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn 0 hfirst]
      rw [hsource_vertex]
      apply PiLp.ext
      intro k
      fin_cases k <;>
        simp [PlanarRot90, AffineMap.lineMap_apply_module] <;>
        ring
    have hzBallNorm : ‖z - γ.source‖ < r₀ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzBall
    have hzBallSq : ‖z - γ.source‖ ^ 2 < r₀ ^ 2 := by
      have hsq := hzBallNorm
      rw [← sq_lt_sq₀ (norm_nonneg _) (le_of_lt hIso.source_pos)] at hsq
      exact hsq
    have hsub : z - γ.source = t • d + s • PlanarRot90 d := by
      rw [hz_chart]
      abel
    have hdisk : t ^ 2 + s ^ 2 <
        (r₀ / dist γ.source γ.vertices[1]) ^ 2 := by
      have hscale :
          (r₀ / dist γ.source γ.vertices[1]) ^ 2 * ‖d‖ ^ 2 = r₀ ^ 2 := by
        rw [hdist_eq_normd]
        field_simp [ne_of_gt hnormd_pos]
      rw [hsub, hnorm_sq] at hzBallSq
      rw [← hscale] at hzBallSq
      have hpos_sq : 0 < ‖d‖ ^ 2 := sq_pos_of_pos hnormd_pos
      exact lt_of_mul_lt_mul_right hzBallSq (le_of_lt hpos_sq)
    have ht_pos : 0 < t := lt_trans (sep.lowerParam_pos 0 hfirst) ht.1
    have hprod_le :
        compatibleTubes.initialConeBound 0 hfirst *
            sep.lowerParam 0 hfirst ≤
          K₀ * t := by
      exact mul_le_mul (le_of_lt hKinit_lt) (le_of_lt ht.1)
        (le_of_lt (sep.lowerParam_pos 0 hfirst)) (le_of_lt hK₀)
    have hwidth_lt_Kt :
        sep.halfWidth 0 hfirst < K₀ * t :=
      lt_of_lt_of_le
        (compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam 0 hfirst)
        hprod_le
    have hs_lower : -K₀ * t < s := by
      linarith [hs.1, hwidth_lt_Kt]
    have hs_upper : s < 0 := hs.2
    have hrev_prev_index :
        γ.vertices.length - 1 - (γ.vertices.length - 2) = 1 := by
      have hlen := γ.length_ge_two
      omega
    rw [PolygonalArcTerminalEndpointLeftCone]
    refine ⟨q, ?_, ?_⟩
    · dsimp [q]
      exact ⟨by simpa using ht_pos,
        by
          simpa [PolygonalArcReverse, List.length_reverse, hrev_prev_index]
            using hdisk,
        by simpa using hs_lower, by simpa using hs_upper⟩
    · simpa [q, d, PolygonalArcReverse, List.length_reverse, hrev_prev_index]
        using hz_chart.symm
  · rintro z ⟨hzRight, hzBall⟩
    rw [show
        sep.rightHalf (γ.vertices.length - 2) hlast =
          sep.rightHalf jlast hlast' by
      rfl] at hzRight
    rw [sep.rightHalf_eq jlast hlast'] at hzRight
    rcases hzRight with ⟨t, ht, s, hs, hz_eq⟩
    let d : EuclideanSpace ℝ (Fin 2) := γ.vertices[jlast] - γ.target
    let q : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then 1 - t else -s)
    have hdist_pos : 0 < dist γ.target γ.vertices[jlast] := by
      have hlen_pos :
          0 < PolygonalArcTerminalEndpointSegmentLength γ :=
        lt_trans hIso.target_pos hIso.target_lt_terminal_length
      simpa [PolygonalArcTerminalEndpointSegmentLength, jlast] using hlen_pos
    have hdist_eq_normd : dist γ.target γ.vertices[jlast] = ‖d‖ := by
      rw [dist_eq_norm]
      dsimp [d]
      have hneg : γ.target - γ.vertices[jlast] =
          -(γ.vertices[jlast] - γ.target) := by
        abel
      rw [hneg, norm_neg]
    have hnormd_pos : 0 < ‖d‖ := by
      simpa [← hdist_eq_normd] using hdist_pos
    have hnorm_sq :
        ‖(1 - t) • d + (-s) • PlanarRot90 d‖ ^ 2 =
          ((1 - t) ^ 2 + (-s) ^ 2) * ‖d‖ ^ 2 := by
      have horth :
          inner ℝ ((1 - t) • d) ((-s) • PlanarRot90 d) = 0 := by
        rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
        ring
      have hpyth :
          ‖(1 - t) • d + (-s) • PlanarRot90 d‖ ^ 2 =
            ‖(1 - t) • d‖ ^ 2 + ‖(-s) • PlanarRot90 d‖ ^ 2 := by
        simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      rw [hpyth, norm_smul, norm_smul, PlanarRot90Norm]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have hz_chart :
        z = γ.target + (1 - t) • d + (-s) • PlanarRot90 d := by
      rw [hz_eq]
      dsimp [d]
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn jlast hlast']
      rw [htarget_last_vertex]
      apply PiLp.ext
      intro k
      fin_cases k <;>
        simp [PlanarRot90, AffineMap.lineMap_apply_module] <;>
        ring
    have hzBallNorm : ‖z - γ.target‖ < r₁ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hzBall
    have hzBallSq : ‖z - γ.target‖ ^ 2 < r₁ ^ 2 := by
      have hsq := hzBallNorm
      rw [← sq_lt_sq₀ (norm_nonneg _) (le_of_lt hIso.target_pos)] at hsq
      exact hsq
    have hsub :
        z - γ.target = (1 - t) • d + (-s) • PlanarRot90 d := by
      rw [hz_chart]
      abel
    have hdisk : (1 - t) ^ 2 + (-s) ^ 2 <
        (r₁ / dist γ.target γ.vertices[jlast]) ^ 2 := by
      have hscale :
          (r₁ / dist γ.target γ.vertices[jlast]) ^ 2 * ‖d‖ ^ 2 = r₁ ^ 2 := by
        rw [hdist_eq_normd]
        field_simp [ne_of_gt hnormd_pos]
      rw [hsub, hnorm_sq] at hzBallSq
      rw [← hscale] at hzBallSq
      have hpos_sq : 0 < ‖d‖ ^ 2 := sq_pos_of_pos hnormd_pos
      exact lt_of_mul_lt_mul_right hzBallSq (le_of_lt hpos_sq)
    have ht_lt_one : t < 1 :=
      lt_trans ht.2 (sep.upperParam_lt_one jlast hlast')
    have hone_sub_pos : 0 < 1 - t := sub_pos.mpr ht_lt_one
    have hparam_le : 1 - sep.upperParam jlast hlast' ≤ 1 - t := by
      exact sub_le_sub_left (le_of_lt ht.2) 1
    have hprod_le :
        compatibleTubes.terminalConeBound jlast hlast' *
            (1 - sep.upperParam jlast hlast') ≤
          K₁ * (1 - t) := by
      have hKterm_lt' :
          compatibleTubes.terminalConeBound jlast hlast' < K₁ := by
        simpa [jlast] using hKterm_lt
      exact mul_le_mul (le_of_lt hKterm_lt') hparam_le
        (by
          have hright :
              0 < 1 - sep.upperParam jlast hlast' := by
            linarith [sep.upperParam_lt_one jlast hlast']
          exact le_of_lt hright)
        (le_of_lt hK₁)
    have hwidth_lt_Kt :
        sep.halfWidth jlast hlast' < K₁ * (1 - t) :=
      lt_of_lt_of_le
        (compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
          jlast hlast')
        hprod_le
    have hs_lower_pos : 0 < -s := by
      linarith [hs.2]
    have hs_upper : -s < K₁ * (1 - t) := by
      linarith [hs.1, hwidth_lt_Kt]
    have hrev_first_index : γ.vertices.length - 1 - 1 = jlast := by
      dsimp [jlast]
      have hlen := γ.length_ge_two
      omega
    rw [PolygonalArcInitialEndpointLeftCone]
    refine ⟨q, ?_, ?_⟩
    · dsimp [q]
      exact ⟨by simpa using hone_sub_pos,
        by
          simpa [PolygonalArcReverse, List.length_reverse, hrev_first_index]
            using hdisk,
        by simpa using hs_lower_pos, by simpa using hs_upper⟩
    · simpa [q, d, PolygonalArcReverse, List.length_reverse, hrev_first_index]
        using hz_chart.symm
