import Util.IncidenceGeometry.PolygonalArcCollarSeparatedTubeData

open Classical
noncomputable section


lemma PolygonalArcCollarSeparatedTubeDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) :
    Nonempty
      (PolygonalArcCollarSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins) := by
  let leftParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  let rightParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    1 - controlRadii.radius ⟨j + 1, hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  let segmentLength : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    dist γ.vertices[j] γ.vertices[j + 1]
  let paramSlack : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (leftParam j hj / 2)
      (min ((1 - rightParam j hj) / 2)
        (forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1))))
  let lowerParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    leftParam j hj - paramSlack j hj
  let upperParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    rightParam j hj + paramSlack j hj
  let halfWidth : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    min (η / (4 * (segmentLength j hj + 1)))
      (forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1)))
  let normal : (j : ℕ) → j + 1 < γ.vertices.length →
      EuclideanSpace ℝ (Fin 2) := fun j hj =>
    WithLp.toLp 2 (fun k : Fin 2 =>
      if k = 0 then -((γ.vertices[j + 1] - γ.vertices[j]) 1)
      else (γ.vertices[j + 1] - γ.vertices[j]) 0)
  let tube : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (halfWidth j hj) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  let leftHalf : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) (halfWidth j hj) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  let rightHalf : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
      ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (0 : ℝ) ∧
        z =
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj}
  have leftParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < leftParam j hj := by
    intro j hj
    simpa [leftParam] using middleSegments.left_parameter_pos j hj
  have leftParam_lt_rightParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        leftParam j hj < rightParam j hj := by
    intro j hj
    simpa [leftParam, rightParam] using
      middleSegments.left_parameter_lt_right_parameter j hj
  have rightParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), rightParam j hj < 1 := by
    intro j hj
    simpa [rightParam] using middleSegments.right_parameter_lt_one j hj
  have one_sub_rightParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < 1 - rightParam j hj := by
    intro j hj
    linarith [rightParam_lt_one j hj]
  have segmentLength_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < segmentLength j hj := by
    intro j hj
    let i0 : Fin γ.vertices.length := ⟨j, Nat.lt_of_succ_lt hj⟩
    let i1 : Fin γ.vertices.length := ⟨j + 1, hj⟩
    have hleft : 0 < controlRadii.radius i0 := controlRadii.radius_pos i0
    have hright : 0 < controlRadii.radius i1 := controlRadii.radius_pos i1
    have hsum :
        controlRadii.radius i0 + controlRadii.radius i1 <
          dist γ.vertices[j] γ.vertices[j + 1] := by
      simpa [i0, i1] using controlRadii.adjacent_radii_sum_lt (j := j) hj
    dsimp [segmentLength]
    nlinarith
  have eta_pos : 0 < η := by
    have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
    have hidx : (0 : ℕ) < γ.vertices.length := by omega
    exact (controlRadii.radius_pos ⟨0, hidx⟩).trans
      (controlRadii.radius_lt_eta ⟨0, hidx⟩)
  have paramSlack_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 < paramSlack j hj := by
    intro j hj
    have hden : 0 < 8 * (segmentLength j hj + 1) := by
      have hD : 0 < segmentLength j hj := segmentLength_pos j hj
      positivity
    dsimp [paramSlack]
    exact lt_min (half_pos (leftParam_pos j hj))
      (lt_min (half_pos (one_sub_rightParam_pos j hj))
        (div_pos (forbiddenMargins.margin_pos j hj) hden))
  have paramSlack_le_left_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤ leftParam j hj / 2 := by
    intro j hj
    dsimp [paramSlack]
    exact min_le_left _ _
  have paramSlack_le_one_sub_right_half :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤ (1 - rightParam j hj) / 2 := by
    intro j hj
    dsimp [paramSlack]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have paramSlack_le_margin_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj ≤
          forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [paramSlack]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have paramSlack_mul_segmentLength_lt_margin_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        paramSlack j hj * segmentLength j hj <
          forbiddenMargins.margin j hj / 4 := by
    intro j hj
    let D : ℝ := segmentLength j hj
    let μ : ℝ := forbiddenMargins.margin j hj
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hμpos : 0 < μ := by
      dsimp [μ]
      exact forbiddenMargins.margin_pos j hj
    have hdenpos : 0 < 8 * (D + 1) := by positivity
    have hscaled :
        μ / (8 * (D + 1)) * D < μ / 4 := by
      have hden_ne : 8 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      paramSlack j hj * segmentLength j hj
          ≤ (μ / (8 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by
                simpa [D, μ] using paramSlack_le_margin_scaled j hj)
              hDnonneg
      _ < μ / 4 := hscaled
  have lowerParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < lowerParam j hj := by
    intro j hj
    have hle := paramSlack_le_left_half j hj
    have hleft := leftParam_pos j hj
    dsimp [lowerParam]
    nlinarith
  have lowerParam_lt_leftParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        lowerParam j hj < leftParam j hj := by
    intro j hj
    dsimp [lowerParam]
    linarith [paramSlack_pos j hj]
  have rightParam_lt_upperParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightParam j hj < upperParam j hj := by
    intro j hj
    dsimp [upperParam]
    linarith [paramSlack_pos j hj]
  have upperParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), upperParam j hj < 1 := by
    intro j hj
    have hle := paramSlack_le_one_sub_right_half j hj
    have hright := rightParam_lt_one j hj
    dsimp [upperParam]
    nlinarith
  have halfWidth_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < halfWidth j hj := by
    intro j hj
    have hD : 0 < segmentLength j hj := segmentLength_pos j hj
    have hden4 : 0 < 4 * (segmentLength j hj + 1) := by positivity
    have hden8 : 0 < 8 * (segmentLength j hj + 1) := by positivity
    dsimp [halfWidth]
    exact lt_min (div_pos eta_pos hden4)
      (div_pos (forbiddenMargins.margin_pos j hj) hden8)
  have halfWidth_le_eta_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤ η / (4 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [halfWidth]
    exact min_le_left _ _
  have halfWidth_le_margin_scaled :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj ≤
          forbiddenMargins.margin j hj / (8 * (segmentLength j hj + 1)) := by
    intro j hj
    dsimp [halfWidth]
    exact min_le_right _ _
  have normal_orthogonal :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        inner ℝ (γ.vertices[j + 1] - γ.vertices[j]) (normal j hj) = 0 := by
    intro j hj
    dsimp [normal]
    rw [PiLp.inner_apply]
    simp
    ring
  have normal_norm_eq_tangent_norm :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ‖normal j hj‖ = ‖γ.vertices[j + 1] - γ.vertices[j]‖ := by
    intro j hj
    dsimp [normal]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp
    ring
  have normal_norm_eq_segment_length :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ‖normal j hj‖ = dist γ.vertices[j] γ.vertices[j + 1] := by
    intro j hj
    calc
      ‖normal j hj‖ = ‖γ.vertices[j + 1] - γ.vertices[j]‖ :=
        normal_norm_eq_tangent_norm j hj
      _ = ‖γ.vertices[j] - γ.vertices[j + 1]‖ := by
        rw [← norm_neg (γ.vertices[j + 1] - γ.vertices[j])]
        congr 1
        abel
      _ = dist γ.vertices[j] γ.vertices[j + 1] := by
        rw [dist_eq_norm]
  have halfWidth_mul_normal_norm_lt_eta :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ < η := by
    intro j hj
    let D : ℝ := segmentLength j hj
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hdenpos : 0 < 4 * (D + 1) := by positivity
    have hscaled : η / (4 * (D + 1)) * D < η := by
      have hden_ne : 4 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      halfWidth j hj * ‖normal j hj‖ =
          halfWidth j hj * D := by
            simp [D, segmentLength, normal_norm_eq_segment_length j hj]
      _ ≤ (η / (4 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by simpa [D] using halfWidth_le_eta_scaled j hj) hDnonneg
      _ < η := hscaled
  have halfWidth_mul_normal_norm_lt_margin_quarter :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        halfWidth j hj * ‖normal j hj‖ <
          forbiddenMargins.margin j hj / 4 := by
    intro j hj
    let D : ℝ := segmentLength j hj
    let μ : ℝ := forbiddenMargins.margin j hj
    have hDpos : 0 < D := by
      dsimp [D]
      exact segmentLength_pos j hj
    have hDnonneg : 0 ≤ D := le_of_lt hDpos
    have hμpos : 0 < μ := by
      dsimp [μ]
      exact forbiddenMargins.margin_pos j hj
    have hdenpos : 0 < 8 * (D + 1) := by positivity
    have hscaled : μ / (8 * (D + 1)) * D < μ / 4 := by
      have hden_ne : 8 * (D + 1) ≠ 0 := ne_of_gt hdenpos
      field_simp [hden_ne]
      nlinarith
    calc
      halfWidth j hj * ‖normal j hj‖ =
          halfWidth j hj * D := by
            simp [D, segmentLength, normal_norm_eq_segment_length j hj]
      _ ≤ (μ / (8 * (D + 1))) * D := by
            exact mul_le_mul_of_nonneg_right
              (by simpa [D, μ] using halfWidth_le_margin_scaled j hj) hDnonneg
      _ < μ / 4 := hscaled
  have dist_lineMap_lineMap_local :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (c₁ c₂ : ℝ),
        dist (AffineMap.lineMap A B c₁) (AffineMap.lineMap A B c₂) =
          dist c₁ c₂ * dist A B := by
    intro A B c₁ c₂
    rw [dist_eq_norm, Real.dist_eq, dist_eq_norm]
    have hvec :
        AffineMap.lineMap A B c₁ - AffineMap.lineMap A B c₂ =
          (c₁ - c₂) • (B - A) := by
      apply PiLp.ext
      intro k
      simp [AffineMap.lineMap_apply_module]
      ring
    rw [hvec, norm_smul, Real.norm_eq_abs]
    have hnorm : ‖B - A‖ = ‖A - B‖ := by
      have hneg : B - A = -(A - B) := by
        abel
      rw [hneg, norm_neg]
    rw [hnorm]
  have real_dist_to_Icc_of_mem_Ioo_expansion :
      ∀ {L R ε t : ℝ}, 0 < ε → L < R →
        t ∈ Set.Ioo (L - ε) (R + ε) →
          ∃ u : ℝ, u ∈ Set.Icc L R ∧ dist t u < ε := by
    intro L R ε t hε hLR ht
    by_cases htL : t < L
    · refine ⟨L, ⟨le_rfl, le_of_lt hLR⟩, ?_⟩
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr htL)]
      linarith [ht.1]
    · by_cases htR : t ≤ R
      · refine ⟨t, ⟨le_of_not_gt htL, htR⟩, ?_⟩
        simpa using hε
      · have hRt : R < t := lt_of_not_ge htR
        refine ⟨R, ⟨le_of_lt hLR, le_rfl⟩, ?_⟩
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hRt)]
        linarith [ht.2]
  have middle_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        middleSegments.middle j hj ⊆ tube j hj := by
    intro j hj z hz
    rw [middleSegments.middle_eq j hj] at hz
    rcases hz with ⟨t, ht, rfl⟩
    dsimp [tube]
    refine ⟨t, ?_, 0, ?_, by simp⟩
    · exact ⟨(lowerParam_lt_leftParam j hj).trans_le ht.1,
        lt_of_le_of_lt ht.2 (rightParam_lt_upperParam j hj)⟩
    · exact ⟨by simpa using halfWidth_pos j hj, halfWidth_pos j hj⟩
  have leftHalf_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        leftHalf j hj ⊆ tube j hj := by
    intro j hj z hz
    dsimp [leftHalf] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    dsimp [tube]
    refine ⟨t, ht, s, ?_, rfl⟩
    exact ⟨lt_trans (neg_neg_of_pos (halfWidth_pos j hj)) hs.1, hs.2⟩
  have rightHalf_subset_tube :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightHalf j hj ⊆ tube j hj := by
    intro j hj z hz
    dsimp [rightHalf] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    dsimp [tube]
    refine ⟨t, ht, s, ?_, rfl⟩
    exact ⟨hs.1, hs.2.trans (halfWidth_pos j hj)⟩
  have tube_subset_eta_neighborhood :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ∀ z ∈ tube j hj, ∃ p ∈ γ.carrier, dist z p < η := by
    intro j hj z hz
    dsimp [tube] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    let p : EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t
    have hpseg : p ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] := by
      rw [segment_eq_image_lineMap]
      refine ⟨t, ?_, rfl⟩
      exact ⟨le_of_lt ((lowerParam_pos j hj).trans ht.1),
        le_of_lt (ht.2.trans (upperParam_lt_one j hj))⟩
    have hpcarrier : p ∈ γ.carrier := by
      rw [γ.carrier_eq]
      exact ⟨j, hj, hpseg⟩
    refine ⟨p, hpcarrier, ?_⟩
    have hs_abs : |s| < halfWidth j hj := abs_lt.mpr hs
    have hdist :
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) p = |s| * ‖normal j hj‖ := by
      have hsub :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj - p =
            s • normal j hj := by
        simp [p]
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    calc
      dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) p = |s| * ‖normal j hj‖ := hdist
      _ ≤ halfWidth j hj * ‖normal j hj‖ := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hs_abs) (norm_nonneg _)
      _ < η := halfWidth_mul_normal_norm_lt_eta j hj
  have tube_point_close_to_middle :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        ∀ z ∈ tube j hj, ∃ p ∈ middleSegments.middle j hj,
          dist z p < forbiddenMargins.margin j hj / 2 := by
    intro j hj z hz
    dsimp [tube] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    obtain ⟨u, huIcc, htu⟩ :=
      real_dist_to_Icc_of_mem_Ioo_expansion
        (L := leftParam j hj) (R := rightParam j hj)
        (ε := paramSlack j hj) (t := t) (paramSlack_pos j hj)
        (leftParam_lt_rightParam j hj) (by
          simpa [lowerParam, upperParam] using ht)
    let p : EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] u
    have hpM : p ∈ middleSegments.middle j hj := by
      rw [middleSegments.middle_eq j hj]
      exact ⟨u, by simpa [leftParam, rightParam] using huIcc, rfl⟩
    refine ⟨p, hpM, ?_⟩
    let q : EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t
    have hs_abs : |s| < halfWidth j hj := abs_lt.mpr hs
    have hperp :
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) q = |s| * ‖normal j hj‖ := by
      have hsub :
          AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj - q =
            s • normal j hj := by
        simp [q]
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    have hperp_lt :
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) q <
          forbiddenMargins.margin j hj / 4 := by
      calc
        dist (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) q = |s| * ‖normal j hj‖ := hperp
        _ ≤ halfWidth j hj * ‖normal j hj‖ := by
          exact mul_le_mul_of_nonneg_right (le_of_lt hs_abs) (norm_nonneg _)
        _ < forbiddenMargins.margin j hj / 4 :=
          halfWidth_mul_normal_norm_lt_margin_quarter j hj
    have hline_lt : dist q p < forbiddenMargins.margin j hj / 4 := by
      have htuD :
          dist t u * segmentLength j hj <
            forbiddenMargins.margin j hj / 4 := by
        have hmul :
            dist t u * segmentLength j hj <
              paramSlack j hj * segmentLength j hj :=
          mul_lt_mul_of_pos_right htu (segmentLength_pos j hj)
        exact hmul.trans (paramSlack_mul_segmentLength_lt_margin_quarter j hj)
      calc
        dist q p =
            dist t u * dist γ.vertices[j] γ.vertices[j + 1] := by
              simpa [q, p] using
                dist_lineMap_lineMap_local γ.vertices[j] γ.vertices[j + 1] t u
        _ = dist t u * segmentLength j hj := by
              simp [segmentLength]
        _ < forbiddenMargins.margin j hj / 4 := htuD
    have htri :
        dist
            (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj) p ≤
          dist
              (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • normal j hj) q +
            dist q p :=
      dist_triangle _ _ _
    calc
      dist
          (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
            s • normal j hj) p
          ≤
        dist
            (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
              s • normal j hj) q +
          dist q p := htri
      _ < forbiddenMargins.margin j hj / 4 +
          forbiddenMargins.margin j hj / 4 := add_lt_add hperp_lt hline_lt
      _ = forbiddenMargins.margin j hj / 2 := by ring
  have tube_disjoint_nonadjacent_segments :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (segment ℝ γ.vertices[k] γ.vertices[k + 1]) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzTube hzSeg
    obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzTube
    have hmargin :=
      forbiddenMargins.middle_segment_separation j hj k hk hgap p hpM z hzSeg
    have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
      simpa [dist_comm] using hpClose
    nlinarith [forbiddenMargins.margin_pos j hj, hmargin, hpClose']
  have tube_disjoint_nonincident_control_disks :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (i : Fin γ.vertices.length),
          i.1 ≠ j → i.1 ≠ j + 1 →
            Disjoint (tube j hj)
              (Metric.closedBall γ.vertices[i.1] (controlRadii.radius i)) := by
    intro j hj i hij hijs
    rw [Set.disjoint_left]
    intro z hzTube hzDisk
    obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzTube
    have hmargin :=
      forbiddenMargins.middle_control_disk_separation j hj i hij hijs p hpM z hzDisk
    have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
      simpa [dist_comm] using hpClose
    nlinarith [forbiddenMargins.margin_pos j hj, hmargin, hpClose']
  have tube_disjoint_nonadjacent_middle_cores :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (middleSegments.middle k hk) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzTube hzMiddle
    exact Set.disjoint_left.mp
      (tube_disjoint_nonadjacent_segments j hj k hk hgap) hzTube
      (middleSegments.middle_subset_segment k hk hzMiddle)
  have tube_disjoint_nonadjacent_tubes :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
        (k : ℕ) (hk : k + 1 < γ.vertices.length),
          (j + 1 < k ∨ k + 1 < j) →
            Disjoint (tube j hj) (tube k hk) := by
    intro j hj k hk hgap
    rw [Set.disjoint_left]
    intro z hzj hzk
    obtain ⟨p, hpM, hpClose⟩ := tube_point_close_to_middle j hj z hzj
    obtain ⟨q, hqM, hqClose⟩ := tube_point_close_to_middle k hk z hzk
    have hgap_sym : k + 1 < j ∨ j + 1 < k := by
      cases hgap with
      | inl h => exact Or.inr h
      | inr h => exact Or.inl h
    have hmj :=
      forbiddenMargins.middle_core_separation j hj k hk hgap p hpM q hqM
    have hmk :=
      forbiddenMargins.middle_core_separation k hk j hj hgap_sym q hqM p hpM
    have hpClose' : dist p z < forbiddenMargins.margin j hj / 2 := by
      simpa [dist_comm] using hpClose
    have hmk' : forbiddenMargins.margin k hk ≤ dist p q := by
      simpa [dist_comm] using hmk
    have htri : dist p q ≤ dist p z + dist z q := dist_triangle p z q
    have hsum :
        dist p q <
          forbiddenMargins.margin j hj / 2 +
            forbiddenMargins.margin k hk / 2 :=
      lt_of_le_of_lt htri (add_lt_add hpClose' hqClose)
    nlinarith [forbiddenMargins.margin_pos j hj,
      forbiddenMargins.margin_pos k hk, hmj, hmk', hsum]
  refine ⟨
    { lowerParam := lowerParam
      upperParam := upperParam
      halfWidth := halfWidth
      normal := normal
      tube := tube
      leftHalf := leftHalf
      rightHalf := rightHalf
      lowerParam_pos := lowerParam_pos
      lowerParam_lt_left_parameter := ?_
      right_parameter_lt_upperParam := ?_
      upperParam_lt_one := upperParam_lt_one
      halfWidth_pos := halfWidth_pos
      normal_orthogonal := normal_orthogonal
      normal_norm_eq_segment_length := normal_norm_eq_segment_length
      halfWidth_mul_normal_norm_lt_eta := halfWidth_mul_normal_norm_lt_eta
      halfWidth_mul_normal_norm_lt_margin_quarter :=
        halfWidth_mul_normal_norm_lt_margin_quarter
      lower_parameter_slack_mul_segment_length_lt_margin_quarter := ?_
      upper_parameter_slack_mul_segment_length_lt_margin_quarter := ?_
      tube_eq := ?_
      leftHalf_eq := ?_
      rightHalf_eq := ?_
      middle_subset_tube := middle_subset_tube
      leftHalf_subset_tube := leftHalf_subset_tube
      rightHalf_subset_tube := rightHalf_subset_tube
      tube_subset_eta_neighborhood := tube_subset_eta_neighborhood
      tube_point_close_to_middle := tube_point_close_to_middle
      tube_disjoint_nonadjacent_segments := tube_disjoint_nonadjacent_segments
      tube_disjoint_nonincident_control_disks :=
        tube_disjoint_nonincident_control_disks
      tube_disjoint_nonadjacent_middle_cores :=
        tube_disjoint_nonadjacent_middle_cores
      tube_disjoint_nonadjacent_tubes :=
        tube_disjoint_nonadjacent_tubes }⟩
  · intro j hj
    simpa [leftParam] using lowerParam_lt_leftParam j hj
  · intro j hj
    simpa [rightParam] using rightParam_lt_upperParam j hj
  · intro j hj
    dsimp [lowerParam, leftParam, segmentLength]
    simpa [sub_sub_cancel] using
      paramSlack_mul_segmentLength_lt_margin_quarter j hj
  · intro j hj
    dsimp [upperParam, rightParam, segmentLength]
    simpa [add_sub_cancel_left] using
      paramSlack_mul_segmentLength_lt_margin_quarter j hj
  · intro j hj
    rfl
  · intro j hj
    rfl
  · intro j hj
    rfl
