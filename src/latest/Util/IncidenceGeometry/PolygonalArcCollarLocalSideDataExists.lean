import Util.IncidenceGeometry.PolygonalArcCollarLocalSideData
import Util.IncidenceGeometry.PolygonalArcCollarCompatibleOrientedTubeDataExists
import Util.IncidenceGeometry.PolygonalArcCollarLocalTopologyDataExists
import Util.IncidenceGeometry.PolygonalArcCollarSeparatedTubeDataExists
import Util.IncidenceGeometry.PolygonalArcCollarVertexLocalPieceDataExists

open Classical
noncomputable section


lemma PolygonalArcCollarLocalSideDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) :
    ∃ orientedTubes :
        PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
          forbiddenMargins,
      ∃ vertexLocalPieces :
          PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
            forbiddenMargins orientedTubes.toPolygonalArcCollarSeparatedTubeData,
        Nonempty
          (PolygonalArcCollarLocalSideData γ controlRadii middleSegments
            forbiddenMargins orientedTubes vertexLocalPieces) := by
  rcases PolygonalArcCollarCompatibleOrientedTubeDataExists γ controlRadii
      middleSegments forbiddenMargins with
    ⟨compatibleTubes⟩
  rcases PolygonalArcCollarVertexLocalPieceDataExists γ controlRadii middleSegments
      forbiddenMargins
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData with
    ⟨vertexLocalPieces⟩
  rcases PolygonalArcCollarLocalTopologyDataExists γ controlRadii middleSegments
      forbiddenMargins compatibleTubes vertexLocalPieces with
    ⟨localTopology⟩
  let sep :=
    compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  have signed_point_not_mem_own_segment :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (t s : ℝ),
        s ≠ 0 →
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • sep.normal j hj ∉
            segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
    intro j hj t s hsne hseg
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨u, _hu, hu_eq⟩
    have hsubeq :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] u -
            AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t =
          s • sep.normal j hj := by
      rw [hu_eq]
      simp
    have hline_sub :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] u -
            AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t =
          (u - t) • (γ.vertices[j + 1] - γ.vertices[j]) := by
      apply PiLp.ext
      intro k
      simp [AffineMap.lineMap_apply_module]
      ring
    have hlinear :
        (u - t) • (γ.vertices[j + 1] - γ.vertices[j]) =
          s • sep.normal j hj := by
      rw [← hline_sub]
      exact hsubeq
    have hinner_zero :
        s * inner ℝ (sep.normal j hj) (sep.normal j hj) = 0 := by
      calc
        s * inner ℝ (sep.normal j hj) (sep.normal j hj) =
            inner ℝ (s • sep.normal j hj) (sep.normal j hj) := by
              rw [real_inner_smul_left]
        _ = inner ℝ ((u - t) • (γ.vertices[j + 1] - γ.vertices[j]))
              (sep.normal j hj) := by
              rw [← hlinear]
        _ = (u - t) *
              inner ℝ (γ.vertices[j + 1] - γ.vertices[j])
                (sep.normal j hj) := by
              rw [real_inner_smul_left]
        _ = 0 := by
              have horth :
                  inner ℝ (γ.vertices[j + 1] - γ.vertices[j])
                      (sep.normal j hj) = 0 := by
                    simpa [sep] using
                      sep.normal_orthogonal j hj
              rw [horth, mul_zero]
    have hdist_pos : 0 < dist γ.vertices[j] γ.vertices[j + 1] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
      have hleft :=
        controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
      have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
      nlinarith
    have hnormal_inner_pos :
        0 < inner ℝ (sep.normal j hj) (sep.normal j hj) := by
      have hnorm_pos : 0 < ‖sep.normal j hj‖ := by
        rw [sep.normal_norm_eq_segment_length j hj]
        exact hdist_pos
      rw [real_inner_self_eq_norm_sq]
      positivity
    have hs_zero : s = 0 := by
      nlinarith
    exact hsne hs_zero
  have signed_point_scalar_eq :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (t₁ s₁ t₂ s₂ : ℝ),
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₁ +
              s₁ • sep.normal j hj =
            AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₂ +
              s₂ • sep.normal j hj →
            s₁ = s₂ := by
    intro j hj t₁ s₁ t₂ s₂ h
    have hmove :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₁ -
            AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₂ =
          (s₂ - s₁) • sep.normal j hj := by
      calc
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₁ -
            AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₂ =
            (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₁ +
                s₁ • sep.normal j hj -
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₂) -
                s₁ • sep.normal j hj := by
              abel
        _ =
            (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₂ +
                s₂ • sep.normal j hj -
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₂) -
                s₁ • sep.normal j hj := by
              rw [h]
        _ = (s₂ - s₁) • sep.normal j hj := by
              rw [sub_smul]
              simp
    have hline_sub :
        AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₁ -
            AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t₂ =
          (t₁ - t₂) • (γ.vertices[j + 1] - γ.vertices[j]) := by
      apply PiLp.ext
      intro k
      simp [AffineMap.lineMap_apply_module]
      ring
    have hlinear :
        (t₁ - t₂) • (γ.vertices[j + 1] - γ.vertices[j]) =
          (s₂ - s₁) • sep.normal j hj := by
      rw [← hline_sub]
      exact hmove
    have hinner_zero :
        (s₂ - s₁) * inner ℝ (sep.normal j hj) (sep.normal j hj) = 0 := by
      calc
        (s₂ - s₁) * inner ℝ (sep.normal j hj) (sep.normal j hj) =
            inner ℝ ((s₂ - s₁) • sep.normal j hj)
              (sep.normal j hj) := by
              rw [real_inner_smul_left]
        _ = inner ℝ ((t₁ - t₂) • (γ.vertices[j + 1] - γ.vertices[j]))
              (sep.normal j hj) := by
              rw [← hlinear]
        _ = (t₁ - t₂) *
              inner ℝ (γ.vertices[j + 1] - γ.vertices[j])
                (sep.normal j hj) := by
              rw [real_inner_smul_left]
        _ = 0 := by
              have horth :
                  inner ℝ (γ.vertices[j + 1] - γ.vertices[j])
                      (sep.normal j hj) = 0 := by
                    simpa [sep] using
                      sep.normal_orthogonal j hj
              rw [horth, mul_zero]
    have hdist_pos : 0 < dist γ.vertices[j] γ.vertices[j + 1] := by
      have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
      have hleft :=
        controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
      have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
      nlinarith
    have hnormal_inner_pos :
        0 < inner ℝ (sep.normal j hj) (sep.normal j hj) := by
      have hnorm_pos : 0 < ‖sep.normal j hj‖ := by
        rw [sep.normal_norm_eq_segment_length j hj]
        exact hdist_pos
      rw [real_inner_self_eq_norm_sq]
      positivity
    have hdiff_zero : s₂ - s₁ = 0 := by
      rcases mul_eq_zero.mp hinner_zero with hdiff | hinner
      · exact hdiff
      · nlinarith
    linarith
  have leftHalf_disjoint_own_segment :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        Disjoint (sep.leftHalf j hj)
          (segment ℝ γ.vertices[j] γ.vertices[j + 1]) := by
    intro j hj
    rw [Set.disjoint_left]
    intro z hzLeft hzSeg
    rw [sep.leftHalf_eq j hj] at hzLeft
    rcases hzLeft with ⟨t, _ht, s, hs, rfl⟩
    exact signed_point_not_mem_own_segment j hj t s (ne_of_gt hs.1) hzSeg
  have rightHalf_disjoint_own_segment :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        Disjoint (sep.rightHalf j hj)
          (segment ℝ γ.vertices[j] γ.vertices[j + 1]) := by
    intro j hj
    rw [Set.disjoint_left]
    intro z hzRight hzSeg
    rw [sep.rightHalf_eq j hj] at hzRight
    rcases hzRight with ⟨t, _ht, s, hs, rfl⟩
    exact signed_point_not_mem_own_segment j hj t s (ne_of_lt hs.2) hzSeg
  have leftHalf_mem_initialSignedCone :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) {z},
        z ∈ sep.leftHalf j hj →
          z ∈
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s ≠ 0 ∧
                |s| < compatibleTubes.initialConeBound j hj * t ∧
                  z =
                    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                      s • sep.normal j hj} := by
    intro j hj z hz
    rw [sep.leftHalf_eq j hj] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    refine ⟨t, ⟨(sep.lowerParam_pos j hj).trans ht.1,
      ht.2.trans (sep.upperParam_lt_one j hj)⟩, s, ne_of_gt hs.1, ?_, rfl⟩
    have hwidth :
        sep.halfWidth j hj <
          compatibleTubes.initialConeBound j hj * sep.lowerParam j hj := by
      simpa [sep] using
        compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam j hj
    have hcone_pos := compatibleTubes.initialConeBound_pos j hj
    have hlower_lt :
        compatibleTubes.initialConeBound j hj * sep.lowerParam j hj <
          compatibleTubes.initialConeBound j hj * t :=
      mul_lt_mul_of_pos_left ht.1 hcone_pos
    have hs_abs : |s| < sep.halfWidth j hj := by
      rw [abs_of_pos hs.1]
      exact hs.2
    exact hs_abs.trans (hwidth.trans hlower_lt)
  have rightHalf_mem_initialSignedCone :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) {z},
        z ∈ sep.rightHalf j hj →
          z ∈
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s ≠ 0 ∧
                |s| < compatibleTubes.initialConeBound j hj * t ∧
                  z =
                    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                      s • sep.normal j hj} := by
    intro j hj z hz
    rw [sep.rightHalf_eq j hj] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    refine ⟨t, ⟨(sep.lowerParam_pos j hj).trans ht.1,
      ht.2.trans (sep.upperParam_lt_one j hj)⟩, s, ne_of_lt hs.2, ?_, rfl⟩
    have hwidth :
        sep.halfWidth j hj <
          compatibleTubes.initialConeBound j hj * sep.lowerParam j hj := by
      simpa [sep] using
        compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam j hj
    have hcone_pos := compatibleTubes.initialConeBound_pos j hj
    have hlower_lt :
        compatibleTubes.initialConeBound j hj * sep.lowerParam j hj <
          compatibleTubes.initialConeBound j hj * t :=
      mul_lt_mul_of_pos_left ht.1 hcone_pos
    have hs_abs : |s| < sep.halfWidth j hj := by
      rw [abs_of_neg hs.2]
      linarith [hs.1]
    exact hs_abs.trans (hwidth.trans hlower_lt)
  have leftHalf_mem_terminalSignedCone :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) {z},
        z ∈ sep.leftHalf j hj →
          z ∈
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s ≠ 0 ∧
                |s| < compatibleTubes.terminalConeBound j hj * (1 - t) ∧
                  z =
                    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                      s • sep.normal j hj} := by
    intro j hj z hz
    rw [sep.leftHalf_eq j hj] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    refine ⟨t, ⟨(sep.lowerParam_pos j hj).trans ht.1,
      ht.2.trans (sep.upperParam_lt_one j hj)⟩, s, ne_of_gt hs.1, ?_, rfl⟩
    have hwidth :
        sep.halfWidth j hj <
          compatibleTubes.terminalConeBound j hj * (1 - sep.upperParam j hj) := by
      simpa [sep] using
        compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
          j hj
    have hcone_pos := compatibleTubes.terminalConeBound_pos j hj
    have hupper_lt :
        compatibleTubes.terminalConeBound j hj * (1 - sep.upperParam j hj) <
          compatibleTubes.terminalConeBound j hj * (1 - t) := by
      exact mul_lt_mul_of_pos_left (by linarith [ht.2]) hcone_pos
    have hs_abs : |s| < sep.halfWidth j hj := by
      rw [abs_of_pos hs.1]
      exact hs.2
    exact hs_abs.trans (hwidth.trans hupper_lt)
  have rightHalf_mem_terminalSignedCone :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) {z},
        z ∈ sep.rightHalf j hj →
          z ∈
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s ≠ 0 ∧
                |s| < compatibleTubes.terminalConeBound j hj * (1 - t) ∧
                  z =
                    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                      s • sep.normal j hj} := by
    intro j hj z hz
    rw [sep.rightHalf_eq j hj] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    refine ⟨t, ⟨(sep.lowerParam_pos j hj).trans ht.1,
      ht.2.trans (sep.upperParam_lt_one j hj)⟩, s, ne_of_lt hs.2, ?_, rfl⟩
    have hwidth :
        sep.halfWidth j hj <
          compatibleTubes.terminalConeBound j hj * (1 - sep.upperParam j hj) := by
      simpa [sep] using
        compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
          j hj
    have hcone_pos := compatibleTubes.terminalConeBound_pos j hj
    have hupper_lt :
        compatibleTubes.terminalConeBound j hj * (1 - sep.upperParam j hj) <
          compatibleTubes.terminalConeBound j hj * (1 - t) := by
      exact mul_lt_mul_of_pos_left (by linarith [ht.2]) hcone_pos
    have hs_abs : |s| < sep.halfWidth j hj := by
      rw [abs_of_neg hs.2]
      linarith [hs.1]
    exact hs_abs.trans (hwidth.trans hupper_lt)
  have leftHalf_mem_initialPositiveCone :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) {z},
        z ∈ sep.leftHalf j hj →
          z ∈
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, 0 < s ∧
                s < compatibleTubes.initialConeBound j hj * t ∧
                  z =
                    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                      s • sep.normal j hj} := by
    intro j hj z hz
    rw [sep.leftHalf_eq j hj] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    refine ⟨t, ⟨(sep.lowerParam_pos j hj).trans ht.1,
      ht.2.trans (sep.upperParam_lt_one j hj)⟩, s, hs.1, ?_, rfl⟩
    have hwidth :
        sep.halfWidth j hj <
          compatibleTubes.initialConeBound j hj * sep.lowerParam j hj := by
      simpa [sep] using
        compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam j hj
    have hcone_pos := compatibleTubes.initialConeBound_pos j hj
    have hlower_lt :
        compatibleTubes.initialConeBound j hj * sep.lowerParam j hj <
          compatibleTubes.initialConeBound j hj * t :=
      mul_lt_mul_of_pos_left ht.1 hcone_pos
    exact hs.2.trans (hwidth.trans hlower_lt)
  have leftHalf_mem_terminalPositiveCone :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) {z},
        z ∈ sep.leftHalf j hj →
          z ∈
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, 0 < s ∧
                s < compatibleTubes.terminalConeBound j hj * (1 - t) ∧
                  z =
                    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                      s • sep.normal j hj} := by
    intro j hj z hz
    rw [sep.leftHalf_eq j hj] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    refine ⟨t, ⟨(sep.lowerParam_pos j hj).trans ht.1,
      ht.2.trans (sep.upperParam_lt_one j hj)⟩, s, hs.1, ?_, rfl⟩
    have hwidth :
        sep.halfWidth j hj <
          compatibleTubes.terminalConeBound j hj * (1 - sep.upperParam j hj) := by
      simpa [sep] using
        compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
          j hj
    have hcone_pos := compatibleTubes.terminalConeBound_pos j hj
    have hupper_lt :
        compatibleTubes.terminalConeBound j hj * (1 - sep.upperParam j hj) <
          compatibleTubes.terminalConeBound j hj * (1 - t) := by
      exact mul_lt_mul_of_pos_left (by linarith [ht.2]) hcone_pos
    exact hs.2.trans (hwidth.trans hupper_lt)
  have rightHalf_mem_initialNegativeCone :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) {z},
        z ∈ sep.rightHalf j hj →
          z ∈
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s < 0 ∧
                |s| < compatibleTubes.initialConeBound j hj * t ∧
                  z =
                    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                      s • sep.normal j hj} := by
    intro j hj z hz
    rw [sep.rightHalf_eq j hj] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    refine ⟨t, ⟨(sep.lowerParam_pos j hj).trans ht.1,
      ht.2.trans (sep.upperParam_lt_one j hj)⟩, s, hs.2, ?_, rfl⟩
    have hwidth :
        sep.halfWidth j hj <
          compatibleTubes.initialConeBound j hj * sep.lowerParam j hj := by
      simpa [sep] using
        compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam j hj
    have hcone_pos := compatibleTubes.initialConeBound_pos j hj
    have hlower_lt :
        compatibleTubes.initialConeBound j hj * sep.lowerParam j hj <
          compatibleTubes.initialConeBound j hj * t :=
      mul_lt_mul_of_pos_left ht.1 hcone_pos
    have hs_abs : |s| < sep.halfWidth j hj := by
      rw [abs_of_neg hs.2]
      linarith [hs.1]
    exact hs_abs.trans (hwidth.trans hlower_lt)
  have rightHalf_mem_terminalNegativeCone :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) {z},
        z ∈ sep.rightHalf j hj →
          z ∈
            {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
              ∃ s : ℝ, s < 0 ∧
                |s| < compatibleTubes.terminalConeBound j hj * (1 - t) ∧
                  z =
                    AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                      s • sep.normal j hj} := by
    intro j hj z hz
    rw [sep.rightHalf_eq j hj] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    refine ⟨t, ⟨(sep.lowerParam_pos j hj).trans ht.1,
      ht.2.trans (sep.upperParam_lt_one j hj)⟩, s, hs.2, ?_, rfl⟩
    have hwidth :
        sep.halfWidth j hj <
          compatibleTubes.terminalConeBound j hj * (1 - sep.upperParam j hj) := by
      simpa [sep] using
        compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
          j hj
    have hcone_pos := compatibleTubes.terminalConeBound_pos j hj
    have hupper_lt :
        compatibleTubes.terminalConeBound j hj * (1 - sep.upperParam j hj) <
          compatibleTubes.terminalConeBound j hj * (1 - t) := by
      exact mul_lt_mul_of_pos_left (by linarith [ht.2]) hcone_pos
    have hs_abs : |s| < sep.halfWidth j hj := by
      rw [abs_of_neg hs.2]
      linarith [hs.1]
    exact hs_abs.trans (hwidth.trans hupper_lt)
  have leftHalf_disjoint_carrier_aux :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        Disjoint (sep.leftHalf j hj) γ.carrier := by
    intro j hj
    rw [Set.disjoint_left]
    intro z hzLeft hzCarrier
    rw [γ.carrier_eq] at hzCarrier
    rcases hzCarrier with ⟨k, hk, hzSeg⟩
    rcases lt_trichotomy k j with hkj | hkj | hjk
    · by_cases hgap : k + 1 < j
      · exact
          (Set.disjoint_left.mp
            (sep.tube_disjoint_nonadjacent_segments j hj k hk (Or.inr hgap))
            (sep.leftHalf_subset_tube j hj hzLeft)) hzSeg
      · have hprev : 0 < j := by omega
        have hk_eq : k = j - 1 := by omega
        have hk_succ : k + 1 = j := by omega
        have hzCone :
            z ∈
              {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
                ∃ s : ℝ, s ≠ 0 ∧
                  |s| < compatibleTubes.initialConeBound j hj * t ∧
                    z =
                      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                        s •
                          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
                            j hj} := by
          simpa [sep] using leftHalf_mem_initialSignedCone j hj hzLeft
        have hzPrev :
            z ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] := by
          have hprev_succ : j - 1 + 1 = j := by omega
          simpa [hk_eq, hprev_succ] using hzSeg
        exact
          (Set.disjoint_left.mp
            (compatibleTubes.initial_signed_cone_disjoint_previous_segment
              j hj hprev) hzCone) hzPrev
    · subst k
      exact
        (Set.disjoint_left.mp (leftHalf_disjoint_own_segment j hj)
          hzLeft) hzSeg
    · by_cases hgap : j + 1 < k
      · exact
          (Set.disjoint_left.mp
            (sep.tube_disjoint_nonadjacent_segments j hj k hk (Or.inl hgap))
            (sep.leftHalf_subset_tube j hj hzLeft)) hzSeg
      · have hk_eq : k = j + 1 := by omega
        have hnext : (j + 1) + 1 < γ.vertices.length := by omega
        have hzCone :
            z ∈
              {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
                ∃ s : ℝ, s ≠ 0 ∧
                  |s| < compatibleTubes.terminalConeBound j hj * (1 - t) ∧
                    z =
                      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                        s •
                          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
                            j hj} := by
          simpa [sep] using leftHalf_mem_terminalSignedCone j hj hzLeft
        have hzNext :
            z ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] := by
          simpa [hk_eq, Nat.add_assoc] using hzSeg
        exact
          (Set.disjoint_left.mp
            (compatibleTubes.terminal_signed_cone_disjoint_next_segment
              j hj hnext) hzCone) hzNext
  have rightHalf_disjoint_carrier_aux :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        Disjoint (sep.rightHalf j hj) γ.carrier := by
    intro j hj
    rw [Set.disjoint_left]
    intro z hzRight hzCarrier
    rw [γ.carrier_eq] at hzCarrier
    rcases hzCarrier with ⟨k, hk, hzSeg⟩
    rcases lt_trichotomy k j with hkj | hkj | hjk
    · by_cases hgap : k + 1 < j
      · exact
          (Set.disjoint_left.mp
            (sep.tube_disjoint_nonadjacent_segments j hj k hk (Or.inr hgap))
            (sep.rightHalf_subset_tube j hj hzRight)) hzSeg
      · have hprev : 0 < j := by omega
        have hk_eq : k = j - 1 := by omega
        have hk_succ : k + 1 = j := by omega
        have hzCone :
            z ∈
              {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
                ∃ s : ℝ, s ≠ 0 ∧
                  |s| < compatibleTubes.initialConeBound j hj * t ∧
                    z =
                      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                        s •
                          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
                            j hj} := by
          simpa [sep] using rightHalf_mem_initialSignedCone j hj hzRight
        have hzPrev :
            z ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] := by
          have hprev_succ : j - 1 + 1 = j := by omega
          simpa [hk_eq, hprev_succ] using hzSeg
        exact
          (Set.disjoint_left.mp
            (compatibleTubes.initial_signed_cone_disjoint_previous_segment
              j hj hprev) hzCone) hzPrev
    · subst k
      exact
        (Set.disjoint_left.mp (rightHalf_disjoint_own_segment j hj)
          hzRight) hzSeg
    · by_cases hgap : j + 1 < k
      · exact
          (Set.disjoint_left.mp
            (sep.tube_disjoint_nonadjacent_segments j hj k hk (Or.inl hgap))
            (sep.rightHalf_subset_tube j hj hzRight)) hzSeg
      · have hk_eq : k = j + 1 := by omega
        have hnext : (j + 1) + 1 < γ.vertices.length := by omega
        have hzCone :
            z ∈
              {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
                ∃ s : ℝ, s ≠ 0 ∧
                  |s| < compatibleTubes.terminalConeBound j hj * (1 - t) ∧
                    z =
                      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                        s •
                          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
                            j hj} := by
          simpa [sep] using rightHalf_mem_terminalSignedCone j hj hzRight
        have hzNext :
            z ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] := by
          simpa [hk_eq, Nat.add_assoc] using hzSeg
        exact
          (Set.disjoint_left.mp
            (compatibleTubes.terminal_signed_cone_disjoint_next_segment
              j hj hnext) hzCone) hzNext
  have leftHalf_disjoint_rightHalf_aux :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          Disjoint (sep.leftHalf j hj) (sep.rightHalf k hk) := by
    intro j hj k hk
    rw [Set.disjoint_left]
    intro z hzLeft hzRight
    rcases lt_trichotomy k j with hkj | hkj | hjk
    · by_cases hgap : k + 1 < j
      · exact
          (Set.disjoint_left.mp
            (sep.tube_disjoint_nonadjacent_tubes j hj k hk (Or.inr hgap))
            (sep.leftHalf_subset_tube j hj hzLeft))
            (sep.rightHalf_subset_tube k hk hzRight)
      · have hj_eq : j = k + 1 := by omega
        subst j
        have hzRightCone :
            z ∈
              {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
                ∃ s : ℝ, s < 0 ∧
                  |s| < compatibleTubes.terminalConeBound k hk * (1 - t) ∧
                    z =
                      AffineMap.lineMap γ.vertices[k] γ.vertices[k + 1] t +
                        s •
                          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
                            k hk} := by
          simpa [sep] using rightHalf_mem_terminalNegativeCone k hk hzRight
        have hzLeftCone :
            z ∈
              {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
                ∃ s : ℝ, 0 < s ∧
                  s < compatibleTubes.initialConeBound (k + 1) hj * t ∧
                    z =
                      AffineMap.lineMap γ.vertices[k + 1]
                        γ.vertices[k + 2] t +
                        s •
                          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
                            (k + 1) hj} := by
          simpa [sep, Nat.add_assoc] using
            leftHalf_mem_initialPositiveCone (k + 1) hj hzLeft
        exact
          (Set.disjoint_left.mp
            (compatibleTubes.successive_negative_positive_cones_disjoint
              k hk hj) hzRightCone) hzLeftCone
    · subst k
      rw [sep.leftHalf_eq j hj] at hzLeft
      rw [sep.rightHalf_eq j hj] at hzRight
      rcases hzLeft with ⟨tL, _htL, sL, hsL, hzL⟩
      rcases hzRight with ⟨tR, _htR, sR, hsR, hzR⟩
      have hsame :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] tL +
              sL • sep.normal j hj =
            AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] tR +
              sR • sep.normal j hj := by
        rw [← hzL, hzR]
      have hs_eq := signed_point_scalar_eq j hj tL sL tR sR hsame
      linarith [hsL.1, hsR.2, hs_eq]
    · by_cases hgap : j + 1 < k
      · exact
          (Set.disjoint_left.mp
            (sep.tube_disjoint_nonadjacent_tubes j hj k hk (Or.inl hgap))
            (sep.leftHalf_subset_tube j hj hzLeft))
            (sep.rightHalf_subset_tube k hk hzRight)
      · have hk_eq : k = j + 1 := by omega
        subst k
        have hzLeftCone :
            z ∈
              {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
                ∃ s : ℝ, 0 < s ∧
                  s < compatibleTubes.terminalConeBound j hj * (1 - t) ∧
                    z =
                      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                        s •
                          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
                            j hj} := by
          simpa [sep] using leftHalf_mem_terminalPositiveCone j hj hzLeft
        have hzRightCone :
            z ∈
              {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
                ∃ s : ℝ, s < 0 ∧
                  |s| < compatibleTubes.initialConeBound (j + 1) hk * t ∧
                    z =
                      AffineMap.lineMap γ.vertices[j + 1]
                        γ.vertices[j + 2] t +
                        s •
                          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
                            (j + 1) hk} := by
          simpa [sep, Nat.add_assoc] using
            rightHalf_mem_initialNegativeCone (j + 1) hk hzRight
        exact
          (Set.disjoint_left.mp
            (compatibleTubes.successive_positive_negative_cones_disjoint
              j hj hk) hzLeftCone) hzRightCone
  refine ⟨compatibleTubes.orientedTubes, vertexLocalPieces, ?_⟩
  exact
    ⟨{ vertexCollar := localTopology.vertexCollar
       leftSidePiece := localTopology.leftSidePiece
       rightSidePiece := localTopology.rightSidePiece
       vertexCollar_open := localTopology.vertexCollar_open
       leftSidePiece_open := localTopology.leftSidePiece_open
       rightSidePiece_open := localTopology.rightSidePiece_open
       vertexCollar_subset_vertexDisk := localTopology.vertexCollar_subset_vertexDisk
       interior_vertexCollar_eq_vertexDisk :=
        localTopology.interior_vertexCollar_eq_vertexDisk
       endpoint_vertexCollar_omits_vertex :=
        localTopology.endpoint_vertexCollar_omits_vertex
       vertexCollar_subset_eta_neighborhood :=
        localTopology.vertexCollar_subset_eta_neighborhood
       vertexCollar_carrier_subset_incident_segments :=
        localTopology.vertexCollar_carrier_subset_incident_segments
       outgoing_germ_subset_vertexCollar :=
        localTopology.outgoing_germ_subset_vertexCollar
       incoming_germ_subset_vertexCollar :=
        localTopology.incoming_germ_subset_vertexCollar
       outgoing_germ_subset_closure_leftSidePiece :=
        localTopology.outgoing_germ_subset_closure_leftSidePiece
       outgoing_germ_subset_closure_rightSidePiece :=
        localTopology.outgoing_germ_subset_closure_rightSidePiece
       incoming_germ_subset_closure_leftSidePiece :=
        localTopology.incoming_germ_subset_closure_leftSidePiece
       incoming_germ_subset_closure_rightSidePiece :=
        localTopology.incoming_germ_subset_closure_rightSidePiece
       interior_vertex_mem_closure_leftSidePiece :=
        localTopology.interior_vertex_mem_closure_leftSidePiece
       interior_vertex_mem_closure_rightSidePiece :=
        localTopology.interior_vertex_mem_closure_rightSidePiece
       leftSidePiece_subset_vertexCollar :=
        localTopology.leftSidePiece_subset_vertexCollar
       rightSidePiece_subset_vertexCollar :=
        localTopology.rightSidePiece_subset_vertexCollar
       leftSidePiece_connected := localTopology.leftSidePiece_connected
       rightSidePiece_connected := localTopology.rightSidePiece_connected
       leftSidePiece_disjoint_carrier :=
        localTopology.leftSidePiece_disjoint_carrier
       rightSidePiece_disjoint_carrier :=
        localTopology.rightSidePiece_disjoint_carrier
       local_sidePieces_disjoint := localTopology.local_sidePieces_disjoint
       leftHalf_disjoint_carrier := by
        simpa [sep] using leftHalf_disjoint_carrier_aux
       rightHalf_disjoint_carrier := by
        simpa [sep] using rightHalf_disjoint_carrier_aux
       leftHalf_disjoint_rightHalf := by
        simpa [sep] using leftHalf_disjoint_rightHalf_aux
       leftHalf_inter_vertexCollar_subset_leftSidePiece :=
        localTopology.leftHalf_inter_vertexCollar_subset_leftSidePiece
       rightHalf_inter_vertexCollar_subset_rightSidePiece :=
        localTopology.rightHalf_inter_vertexCollar_subset_rightSidePiece
       vertexCollar_without_arc := localTopology.vertexCollar_without_arc
       outgoingLeftAttachment_subset_leftSidePiece :=
        localTopology.outgoingLeftAttachment_subset_leftSidePiece
       outgoingRightAttachment_subset_rightSidePiece :=
        localTopology.outgoingRightAttachment_subset_rightSidePiece
       incomingLeftAttachment_subset_leftSidePiece :=
        localTopology.incomingLeftAttachment_subset_leftSidePiece
       incomingRightAttachment_subset_rightSidePiece :=
        localTopology.incomingRightAttachment_subset_rightSidePiece }⟩
