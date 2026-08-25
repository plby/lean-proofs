import Util.IncidenceGeometry.PolygonalArcCollarMiddleForbiddenMargins
import Util.IncidenceGeometry.PolygonalArcCollarMiddleTubeData

structure PolygonalArcCollarSeparatedTubeData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments) where
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
  halfWidth_mul_normal_norm_lt_margin_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      halfWidth j hj * ‖normal j hj‖ <
        forbiddenMargins.margin j hj / 4
  lower_parameter_slack_mul_segment_length_lt_margin_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1] -
          lowerParam j hj) *
        dist γ.vertices[j] γ.vertices[j + 1] <
          forbiddenMargins.margin j hj / 4
  upper_parameter_slack_mul_segment_length_lt_margin_quarter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (upperParam j hj -
          (1 - controlRadii.radius ⟨j + 1, hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1])) *
        dist γ.vertices[j] γ.vertices[j + 1] <
          forbiddenMargins.margin j hj / 4
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
  tube_point_close_to_middle :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      ∀ z ∈ tube j hj, ∃ p ∈ middleSegments.middle j hj,
        dist z p < forbiddenMargins.margin j hj / 2
  tube_disjoint_nonadjacent_segments :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (j + 1 < k ∨ k + 1 < j) →
          Disjoint (tube j hj) (segment ℝ γ.vertices[k] γ.vertices[k + 1])
  tube_disjoint_nonincident_control_disks :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (i : Fin γ.vertices.length),
        i.1 ≠ j → i.1 ≠ j + 1 →
          Disjoint (tube j hj)
            (Metric.closedBall γ.vertices[i.1] (controlRadii.radius i))
  tube_disjoint_nonadjacent_middle_cores :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (j + 1 < k ∨ k + 1 < j) →
          Disjoint (tube j hj) (middleSegments.middle k hk)
  tube_disjoint_nonadjacent_tubes :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length)
      (k : ℕ) (hk : k + 1 < γ.vertices.length),
        (j + 1 < k ∨ k + 1 < j) →
          Disjoint (tube j hj) (tube k hk)
