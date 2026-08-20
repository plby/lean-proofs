import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleSegmentData

-- [TABLET NODE: PolygonalArcCollarMiddleTubeData]
structure PolygonalArcCollarMiddleTubeData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii) where
-- BODY
  lowerParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  upperParam : (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  halfWidth : (j : ℕ) → j + 1 < γ.vertices.length → ℝ
  normal : (j : ℕ) → j + 1 < γ.vertices.length → EuclideanSpace ℝ (Fin 2)
  tube : (j : ℕ) → j + 1 < γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  leftHalf : (j : ℕ) → j + 1 < γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  rightHalf : (j : ℕ) → j + 1 < γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  lowerParam_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < lowerParam j hj
  lowerParam_lt_left_parameter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      lowerParam j hj <
        controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1]
  right_parameter_lt_upperParam :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      1 - controlRadii.radius ⟨j + 1, hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1] <
        upperParam j hj
  upperParam_lt_one :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), upperParam j hj < 1
  halfWidth_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length), 0 < halfWidth j hj
  normal_orthogonal :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      inner ℝ (γ.vertices[j + 1] - γ.vertices[j]) (normal j hj) = 0
  normal_norm_eq_segment_length :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      ‖normal j hj‖ = dist γ.vertices[j] γ.vertices[j + 1]
  halfWidth_mul_normal_norm_lt_eta :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      halfWidth j hj * ‖normal j hj‖ < η
  tube_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      tube j hj =
        {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
          ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (halfWidth j hj) ∧
            z =
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • normal j hj}
  leftHalf_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      leftHalf j hj =
        {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
          ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) (halfWidth j hj) ∧
            z =
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • normal j hj}
  rightHalf_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      rightHalf j hj =
        {z | ∃ t : ℝ, t ∈ Set.Ioo (lowerParam j hj) (upperParam j hj) ∧
          ∃ s : ℝ, s ∈ Set.Ioo (-(halfWidth j hj)) (0 : ℝ) ∧
            z =
              AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1] t +
                s • normal j hj}
  middle_subset_tube :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      middleSegments.middle j hj ⊆ tube j hj
  leftHalf_subset_tube :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      leftHalf j hj ⊆ tube j hj
  rightHalf_subset_tube :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      rightHalf j hj ⊆ tube j hj
  tube_subset_eta_neighborhood :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      ∀ z ∈ tube j hj, ∃ p ∈ γ.carrier, dist z p < η
