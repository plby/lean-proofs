import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow
import ErdosProblems.Erdos733.ST.PolygonalArcCollarControlRadii
import ErdosProblems.Erdos733.ST.PolygonalArcCollarControlRadiiExistsBelow
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalSideDataExistsWithEndpointCaps
import ErdosProblems.Erdos733.ST.PolygonalArcCollarLocalTopologyDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleForbiddenMarginsExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleSegmentData
import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleSegmentDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcCollarVertexLocalPieceDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointDiskCappedTaperChartTransport
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolation
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointDiskCappedTaperSideLabelling
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointCone
import ErdosProblems.Erdos733.ST.PolygonalArcInitialEndpointSegmentLength
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling
import ErdosProblems.Erdos733.ST.PolygonalArcSideStripAssembly
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointCone
import ErdosProblems.Erdos733.ST.PolygonalArcTerminalEndpointSegmentLength
import ErdosProblems.Erdos733.ST.PolygonalArcVertexNonincidentSegmentSeparation
import ErdosProblems.Erdos733.ST.PlanarRot90ConeAvoidsRay
import ErdosProblems.Erdos733.ST.PlanarRot90SameSideConesDisjoint
import ErdosProblems.Erdos733.ST.PolygonalSideStrips
import ErdosProblems.Erdos733.ST.PositiveSeparation

open Classical
noncomputable section


-- [TABLET NODE: PolygonalArcCappedCollarAssemblyExists]
lemma PolygonalArcCappedCollarAssemblyExists (γ : PolygonalArc)
    (η r₀ r₁ K₀ K₁ : ℝ) :
    0 < η →
      PolygonalArcEndpointIsolation γ r₀ r₁ →
        0 < K₀ →
          0 < K₁ →
              ∃ S : PolygonalSideStrips γ,
                γ.source ∉ S.collar ∧
                  γ.target ∉ S.collar ∧
                    ((S.collar ∩ Metric.ball γ.source r₀) \
                        γ.relativeInterior ⊆
                      PolygonalArcInitialEndpointCone γ r₀ K₀) ∧
                      ((S.collar ∩ Metric.ball γ.target r₁) \
                          γ.relativeInterior ⊆
                        PolygonalArcTerminalEndpointCone γ r₁ K₁) ∧
                        ∀ z ∈ S.collar, ∃ p ∈ γ.carrier, dist z p < η := by
-- BODY
  intro hη hIso hK₀ hK₁
  have hsourceIdx : 0 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  have hfirst : 0 + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  have hfirst' : 1 < γ.vertices.length := by
    simpa using hfirst
  let itarget : ℕ := γ.vertices.length - 1
  have htargetIdx : itarget < γ.vertices.length := by
    have hlen := γ.length_ge_two
    dsimp [itarget]
    omega
  let jlast : ℕ := γ.vertices.length - 2
  have hlast : jlast + 1 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    dsimp [jlast]
    omega
  have hlast_succ : jlast + 1 = itarget := by
    have hlen := γ.length_ge_two
    dsimp [jlast, itarget]
    omega
  have hsource_vertex : γ.vertices[0] = γ.source := by
    have hget : γ.vertices[0]? = some γ.vertices[0] :=
      List.getElem?_eq_getElem hsourceIdx
    rw [← List.head?_eq_getElem?, γ.source_eq_head] at hget
    exact Option.some.inj hget.symm
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
  obtain ⟨controlRadii, hρ0_lt, hρT_lt, hsourceBalls, htargetBalls⟩ :=
    PolygonalArcCollarControlRadiiExistsBelow γ η r₀ r₁ hη hIso.source_pos
      hIso.target_pos hIso
  obtain ⟨middleSegments⟩ :=
    PolygonalArcCollarMiddleSegmentDataExists γ controlRadii
  obtain ⟨forbiddenMargins⟩ :=
    PolygonalArcCollarMiddleForbiddenMarginsExists γ controlRadii middleSegments
  obtain ⟨compatibleTubes, hKinit_lt, hKterm_lt, htubeSourceDisj,
      htubeTargetDisj⟩ :=
    PolygonalArcCollarCompatibleOrientedTubeDataExistsBelow γ controlRadii
      middleSegments forbiddenMargins r₀ r₁ K₀ K₁ hIso hK₀ hK₁
  obtain ⟨vertexLocalPieces, localSideData, hsourceVertexOmit,
      htargetVertexOmit, hsourceVertexCone, htargetVertexCone,
      hvertexSourceDisj, hvertexTargetDisj⟩ :=
    PolygonalArcCollarLocalSideDataExistsWithEndpointCaps γ controlRadii
      middleSegments forbiddenMargins compatibleTubes r₀ r₁ K₀ K₁
      hIso.source_pos hIso.target_pos hK₀ hK₁ hρ0_lt hρT_lt hKinit_lt
      hKterm_lt hsourceBalls htargetBalls
  obtain ⟨S, hcollar_eq, _hleft_eq, _hright_eq, hnear⟩ :=
    PolygonalArcSideStripAssembly γ controlRadii middleSegments forbiddenMargins
      compatibleTubes.orientedTubes vertexLocalPieces localSideData
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  have hsourceCarrier : γ.source ∈ γ.carrier := by
    have hvertex : γ.vertices[0] ∈ γ.carrier :=
      PolygonalArcVertexMemCarrier γ
        (List.getElem_mem (l := γ.vertices) hsourceIdx)
    simpa [hsource_vertex] using hvertex
  have htargetCarrier : γ.target ∈ γ.carrier := by
    have hvertex : γ.vertices[itarget] ∈ γ.carrier :=
      PolygonalArcVertexMemCarrier γ
        (List.getElem_mem (l := γ.vertices) htargetIdx)
    simpa [htarget_vertex] using hvertex
  have hsource_not_relint : γ.source ∉ γ.relativeInterior := by
    intro hrel
    rw [γ.relativeInterior_eq] at hrel
    exact hrel.2 (by simp)
  have htarget_not_relint : γ.target ∉ γ.relativeInterior := by
    intro hrel
    rw [γ.relativeInterior_eq] at hrel
    exact hrel.2 (by simp)
  have hsource_not_collar : γ.source ∉ S.collar := by
    intro hS
    have hwithout : γ.source ∈ S.collar \ γ.relativeInterior :=
      ⟨hS, hsource_not_relint⟩
    have hside : γ.source ∈ S.leftStrip ∪ S.rightStrip := by
      simpa [S.collar_without_arc] using hwithout
    rcases hside with hleft | hright
    · exact (Set.disjoint_left.mp S.left_disjoint_arc hleft) hsourceCarrier
    · exact (Set.disjoint_left.mp S.right_disjoint_arc hright) hsourceCarrier
  have htarget_not_collar : γ.target ∉ S.collar := by
    intro hS
    have hwithout : γ.target ∈ S.collar \ γ.relativeInterior :=
      ⟨hS, htarget_not_relint⟩
    have hside : γ.target ∈ S.leftStrip ∪ S.rightStrip := by
      simpa [S.collar_without_arc] using hwithout
    rcases hside with hleft | hright
    · exact (Set.disjoint_left.mp S.left_disjoint_arc hleft) htargetCarrier
    · exact (Set.disjoint_left.mp S.right_disjoint_arc hright) htargetCarrier
  have hinitialTubeCone :
      sep.tube 0 hfirst ∩ Metric.ball γ.source r₀ ⊆
        PolygonalArcInitialEndpointCone γ r₀ K₀ := by
    rintro z ⟨hzTube, hzBall⟩
    rw [sep.tube_eq 0 hfirst] at hzTube
    rcases hzTube with ⟨t, ht, s, hs, hz_eq⟩
    let d : EuclideanSpace ℝ (Fin 2) := γ.vertices[1] - γ.source
    let q : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then t else s)
    have hdist_pos : 0 < dist γ.source γ.vertices[1] := by
      have hlen_pos :
          0 < PolygonalArcInitialEndpointSegmentLength γ :=
        lt_trans hIso.source_pos hIso.source_lt_initial_length
      simpa [PolygonalArcInitialEndpointSegmentLength] using hlen_pos
    have hd_ne : d ≠ 0 := by
      intro hd
      have hdist_zero : dist γ.source γ.vertices[1] = 0 := by
        rw [dist_eq_zero]
        exact sub_eq_zero.mp hd |>.symm
      linarith
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
      nlinarith
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
    have hs_upper : s < K₀ * t := lt_trans hs.2 hwidth_lt_Kt
    rw [PolygonalArcInitialEndpointCone]
    refine ⟨q, ?_, ?_⟩
    · dsimp [q]
      exact ⟨by simpa using ht_pos, by simpa using hdisk,
        by simpa using hs_lower, by simpa using hs_upper⟩
    · simpa [q, d, hsource_vertex] using hz_chart.symm
  have hterminalTubeCone :
      sep.tube jlast hlast ∩ Metric.ball γ.target r₁ ⊆
        PolygonalArcTerminalEndpointCone γ r₁ K₁ := by
    rintro z ⟨hzTube, hzBall⟩
    rw [sep.tube_eq jlast hlast] at hzTube
    rcases hzTube with ⟨t, ht, s, hs, hz_eq⟩
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
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn jlast hlast]
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
      nlinarith
    have ht_lt_one : t < 1 :=
      lt_trans ht.2 (sep.upperParam_lt_one jlast hlast)
    have hone_sub_pos : 0 < 1 - t := by linarith
    have hparam_le : 1 - sep.upperParam jlast hlast ≤ 1 - t := by
      linarith [ht.2]
    have hprod_le :
        compatibleTubes.terminalConeBound jlast hlast *
            (1 - sep.upperParam jlast hlast) ≤
          K₁ * (1 - t) := by
      exact mul_le_mul (le_of_lt hKterm_lt) hparam_le
        (by
          have hright :
              0 < 1 - sep.upperParam jlast hlast := by
            linarith [sep.upperParam_lt_one jlast hlast]
          exact le_of_lt hright)
        (le_of_lt hK₁)
    have hwidth_lt_Kt :
        sep.halfWidth jlast hlast < K₁ * (1 - t) :=
      lt_of_lt_of_le
        (compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
          jlast hlast)
        hprod_le
    have hs_lower : -K₁ * (1 - t) < -s := by
      linarith [hs.2, hwidth_lt_Kt]
    have hs_upper : -s < K₁ * (1 - t) := by
      linarith [hs.1, hwidth_lt_Kt]
    rw [PolygonalArcTerminalEndpointCone]
    refine ⟨q, ?_, ?_⟩
    · dsimp [q]
      exact ⟨by simpa using hone_sub_pos, by simpa using hdisk,
        by simpa using hs_lower, by simpa using hs_upper⟩
    · simpa [q, d, jlast, hlast_succ, htarget_last_vertex] using hz_chart.symm
  have hinitialContain :
      ((S.collar ∩ Metric.ball γ.source r₀) \ γ.relativeInterior ⊆
        PolygonalArcInitialEndpointCone γ r₀ K₀) := by
    rintro z ⟨⟨hzS, hzBall⟩, hzNotRel⟩
    have hzUnion : z ∈
        ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.tube j hj) ∪
          (⋃ i : Fin γ.vertices.length, localSideData.vertexCollar i)) := by
      simpa [sep, hcollar_eq] using hzS
    rcases hzUnion with hzTubes | hzVertices
    · rcases Set.mem_iUnion.1 hzTubes with ⟨j, hzj⟩
      rcases Set.mem_iUnion.1 hzj with ⟨hj, hzTube⟩
      by_cases hj0 : j = 0
      · subst j
        exact hinitialTubeCone ⟨by simpa using hzTube, hzBall⟩
      · exact False.elim
          ((Set.disjoint_left.mp (htubeSourceDisj j hj hj0)) hzTube hzBall)
    · rcases Set.mem_iUnion.1 hzVertices with ⟨i, hzVertex⟩
      by_cases hi0 : i.1 = 0
      · have hi_eq : i = ⟨0, hsourceIdx⟩ := Fin.ext hi0
        subst i
        exact hsourceVertexCone ⟨by simpa using hzVertex, hzNotRel⟩
      · exact False.elim
          ((Set.disjoint_left.mp (hvertexSourceDisj i hi0)) hzVertex hzBall)
  have hterminalContain :
      ((S.collar ∩ Metric.ball γ.target r₁) \ γ.relativeInterior ⊆
        PolygonalArcTerminalEndpointCone γ r₁ K₁) := by
    rintro z ⟨⟨hzS, hzBall⟩, hzNotRel⟩
    have hzUnion : z ∈
        ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.tube j hj) ∪
          (⋃ i : Fin γ.vertices.length, localSideData.vertexCollar i)) := by
      simpa [sep, hcollar_eq] using hzS
    rcases hzUnion with hzTubes | hzVertices
    · rcases Set.mem_iUnion.1 hzTubes with ⟨j, hzj⟩
      rcases Set.mem_iUnion.1 hzj with ⟨hj, hzTube⟩
      by_cases hjlast : j = jlast
      · subst j
        exact hterminalTubeCone ⟨by simpa using hzTube, hzBall⟩
      · exact False.elim
          ((Set.disjoint_left.mp (htubeTargetDisj j hj hjlast)) hzTube hzBall)
    · rcases Set.mem_iUnion.1 hzVertices with ⟨i, hzVertex⟩
      by_cases hitarget : i.1 + 1 = γ.vertices.length
      · have hi_eq : i = ⟨itarget, htargetIdx⟩ := by
          apply Fin.ext
          dsimp [itarget]
          omega
        subst i
        exact htargetVertexCone ⟨by simpa using hzVertex, hzNotRel⟩
      · exact False.elim
          ((Set.disjoint_left.mp (hvertexTargetDisj i hitarget)) hzVertex hzBall)
  exact ⟨S, hsource_not_collar, htarget_not_collar, hinitialContain,
    hterminalContain, hnear⟩
