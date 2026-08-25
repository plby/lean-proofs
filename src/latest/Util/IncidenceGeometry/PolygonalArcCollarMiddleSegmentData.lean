import Util.IncidenceGeometry.PolygonalArcCollarControlRadii

structure PolygonalArcCollarMiddleSegmentData (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) where
  middle : (j : ℕ) → j + 1 < γ.vertices.length → Set (EuclideanSpace ℝ (Fin 2))
  left_parameter_pos :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      0 <
        controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1]
  left_parameter_lt_right_parameter :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1] <
        1 - controlRadii.radius ⟨j + 1, hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1]
  right_parameter_lt_one :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      1 - controlRadii.radius ⟨j + 1, hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1] < 1
  middle_eq :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      middle j hj =
        (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Icc
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1])
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1])
  middle_nonempty :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      (middle j hj).Nonempty
  middle_compact :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      IsCompact (middle j hj)
  middle_subset_segment :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      middle j hj ⊆ segment ℝ γ.vertices[j] γ.vertices[j + 1]
  middle_subset_carrier :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      middle j hj ⊆ γ.carrier
  middle_subset_eta_neighborhood :
    ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      ∀ z ∈ middle j hj, ∃ p ∈ γ.carrier, dist z p < η
