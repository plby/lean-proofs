import Util.IncidenceGeometry.PolygonalArcCollarMiddleTubeData

open Classical
noncomputable section


lemma PolygonalArcCollarMiddleTubeDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii) :
    Nonempty (PolygonalArcCollarMiddleTubeData γ controlRadii middleSegments) := by
  let leftParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  let rightParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    1 - controlRadii.radius ⟨j + 1, hj⟩ /
      dist γ.vertices[j] γ.vertices[j + 1]
  let lowerParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    leftParam j hj / 2
  let upperParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    (1 + rightParam j hj) / 2
  let halfWidth : (j : ℕ) → j + 1 < γ.vertices.length → ℝ := fun j hj =>
    η / (4 * (dist γ.vertices[j] γ.vertices[j + 1] + 1))
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
  have lowerParam_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < lowerParam j hj := by
    intro j hj
    dsimp [lowerParam]
    exact half_pos (leftParam_pos j hj)
  have lowerParam_lt_leftParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        lowerParam j hj < leftParam j hj := by
    intro j hj
    dsimp [lowerParam]
    exact half_lt_self (leftParam_pos j hj)
  have rightParam_lt_upperParam :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        rightParam j hj < upperParam j hj := by
    intro j hj
    dsimp [upperParam]
    linarith [rightParam_lt_one j hj]
  have upperParam_lt_one :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), upperParam j hj < 1 := by
    intro j hj
    dsimp [upperParam]
    linarith [rightParam_lt_one j hj]
  have halfWidth_pos :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < halfWidth j hj := by
    intro j hj
    have hηpos : 0 < η :=
      (controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩).trans
        (controlRadii.radius_lt_eta ⟨j, Nat.lt_of_succ_lt hj⟩)
    have hden : 0 < 4 * (dist γ.vertices[j] γ.vertices[j + 1] + 1) := by
      positivity
    dsimp [halfWidth]
    exact div_pos hηpos hden
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
    have hηpos : 0 < η :=
      (controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩).trans
        (controlRadii.radius_lt_eta ⟨j, Nat.lt_of_succ_lt hj⟩)
    let D : ℝ := dist γ.vertices[j] γ.vertices[j + 1]
    have hDnonneg : 0 ≤ D := by
      dsimp [D]
      positivity
    have hdenpos : 0 < 4 * (D + 1) := by
      positivity
    have hD_lt : D < 4 * (D + 1) := by
      nlinarith
    have hmul_lt : η * D < η * (4 * (D + 1)) := by
      exact mul_lt_mul_of_pos_left hD_lt hηpos
    have hden_ne : 4 * (D + 1) ≠ 0 := ne_of_gt hdenpos
    have hcalc : η / (4 * (D + 1)) * D < η := by
      field_simp [hden_ne]
      nlinarith
    simpa [halfWidth, normal_norm_eq_segment_length j hj, D, mul_comm, mul_left_comm,
      mul_assoc] using hcalc
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
      tube_eq := ?_
      leftHalf_eq := ?_
      rightHalf_eq := ?_
      middle_subset_tube := ?_
      leftHalf_subset_tube := ?_
      rightHalf_subset_tube := ?_
      tube_subset_eta_neighborhood := ?_ }⟩
  · intro j hj
    simpa [leftParam] using lowerParam_lt_leftParam j hj
  · intro j hj
    simpa [rightParam] using rightParam_lt_upperParam j hj
  · intro j hj
    rfl
  · intro j hj
    rfl
  · intro j hj
    rfl
  · intro j hj z hz
    rw [middleSegments.middle_eq j hj] at hz
    rcases hz with ⟨t, ht, rfl⟩
    dsimp [tube]
    refine ⟨t, ?_, 0, ?_, by simp⟩
    · exact ⟨(lowerParam_lt_leftParam j hj).trans_le ht.1,
        lt_of_le_of_lt ht.2 (rightParam_lt_upperParam j hj)⟩
    · exact ⟨by simpa using halfWidth_pos j hj, halfWidth_pos j hj⟩
  · intro j hj z hz
    dsimp [leftHalf] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    dsimp [tube]
    refine ⟨t, ht, s, ?_, rfl⟩
    exact ⟨lt_trans (neg_neg_of_pos (halfWidth_pos j hj)) hs.1, hs.2⟩
  · intro j hj z hz
    dsimp [rightHalf] at hz
    rcases hz with ⟨t, ht, s, hs, rfl⟩
    dsimp [tube]
    refine ⟨t, ht, s, ?_, rfl⟩
    exact ⟨hs.1, hs.2.trans (halfWidth_pos j hj)⟩
  · intro j hj z hz
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
