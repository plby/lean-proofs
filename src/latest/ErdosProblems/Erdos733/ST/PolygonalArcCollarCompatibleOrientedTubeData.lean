import ErdosProblems.Erdos733.ST.PolygonalArcCollarOrientedSeparatedTubeData

-- [TABLET NODE: PolygonalArcCollarCompatibleOrientedTubeData]
structure PolygonalArcCollarCompatibleOrientedTubeData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) where
-- BODY
  orientedTubes :
    PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
      forbiddenMargins
  initialConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  terminalConeBound : (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  initialConeBound_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < initialConeBound j hj
  terminalConeBound_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < terminalConeBound j hj
  initial_halfWidth_lt_cone_mul_lowerParam :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth j hj <
        initialConeBound j hj *
          orientedTubes.toPolygonalArcCollarSeparatedTubeData.lowerParam j hj
  terminal_halfWidth_lt_cone_mul_one_sub_upperParam :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth j hj <
        terminalConeBound j hj *
          (1 - orientedTubes.toPolygonalArcCollarSeparatedTubeData.upperParam j hj)
  initial_signed_cone_disjoint_previous_segment :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (_hprev : 0 < j),
      Disjoint
        {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
          ∃ s : ℝ, s ≠ 0 ∧ |s| < initialConeBound j hj * t ∧
            z =
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj}
        (segment ℝ γ.vertices[j - 1] γ.vertices[j])
  terminal_signed_cone_disjoint_next_segment :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (_hnext : (j + 1) + 1 < γ.vertices.length),
        Disjoint
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, s ≠ 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
              z =
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                  s • orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj}
          (segment ℝ γ.vertices[j + 1] γ.vertices[j + 2])
  successive_positive_negative_cones_disjoint :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        Disjoint
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, 0 < s ∧ s < terminalConeBound j hj * (1 - t) ∧
              z =
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                  s • orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj}
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, s < 0 ∧ |s| < initialConeBound (j + 1) hnext * t ∧
              z =
                AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                  s •
                    orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
                      (j + 1) hnext}
  successive_negative_positive_cones_disjoint :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        Disjoint
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, s < 0 ∧ |s| < terminalConeBound j hj * (1 - t) ∧
              z =
                AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                  s • orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj}
          {z | ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧
            ∃ s : ℝ, 0 < s ∧ s < initialConeBound (j + 1) hnext * t ∧
              z =
                AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] t +
                  s •
                    orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
                      (j + 1) hnext}
  initialAwaySeparation :
    (j : ℕ) → (hj : j + 1 < γ.vertices.length) → 0 < j → ℝ
  terminalAwaySeparation :
    ∀ (j : ℕ) (_hj : j + 1 < γ.vertices.length)
      (_hnext : (j + 1) + 1 < γ.vertices.length), ℝ
  successiveAwaySeparation :
    ∀ (j : ℕ) (_hj : j + 1 < γ.vertices.length)
      (_hnext : (j + 1) + 1 < γ.vertices.length), ℝ
  initialAwaySeparation_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      0 < initialAwaySeparation j hj hprev
  terminalAwaySeparation_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        0 < terminalAwaySeparation j hj hnext
  successiveAwaySeparation_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        0 < successiveAwaySeparation j hj hnext
  initial_centerline_previous_segment_away :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      ∀ t : ℝ,
        t ∈ Set.Icc
          (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) →
          ∀ q, q ∈ segment ℝ γ.vertices[j - 1] γ.vertices[j] →
            initialAwaySeparation j hj hprev ≤
              dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q
  terminal_centerline_next_segment_away :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ)
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) →
            ∀ q, q ∈ segment ℝ γ.vertices[j + 1] γ.vertices[j + 2] →
              terminalAwaySeparation j hj hnext ≤
                dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t) q
  successive_centerlines_away :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        ∀ t : ℝ,
          t ∈ Set.Icc (0 : ℝ)
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) →
            ∀ u : ℝ,
              u ∈ Set.Icc
                (controlRadii.radius ⟨j + 1, hj⟩ /
                  dist γ.vertices[j + 1] γ.vertices[j + 2]) (1 : ℝ) →
                successiveAwaySeparation j hj hnext ≤
                  dist
                    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t)
                    (AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 2] u)
  initial_halfWidth_mul_normal_norm_lt_away_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length) (hprev : 0 < j),
      orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth j hj *
          ‖orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj‖ <
        initialAwaySeparation j hj hprev / 4
  terminal_halfWidth_mul_normal_norm_lt_away_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth j hj *
            ‖orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj‖ <
          terminalAwaySeparation j hj hnext / 4
  successive_halfWidth_normal_sum_lt_away_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (hnext : (j + 1) + 1 < γ.vertices.length),
        orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth j hj *
            ‖orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal j hj‖ +
          orientedTubes.toPolygonalArcCollarSeparatedTubeData.halfWidth
              (j + 1) hnext *
            ‖orientedTubes.toPolygonalArcCollarSeparatedTubeData.normal
              (j + 1) hnext‖ <
          successiveAwaySeparation j hj hnext / 4
