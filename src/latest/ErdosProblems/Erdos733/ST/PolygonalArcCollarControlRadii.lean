import ErdosProblems.Erdos733.ST.PolygonalArc

-- [TABLET NODE: PolygonalArcCollarControlRadii]
structure PolygonalArcCollarControlRadii (γ : PolygonalArc) (η : ℝ) where
-- BODY
  radius : Fin γ.vertices.length → ℝ
  radius_pos : ∀ i, 0 < radius i
  radius_lt_eta : ∀ i, radius i < η
  control_disks_disjoint :
    ∀ ⦃i j : Fin γ.vertices.length⦄, i ≠ j →
      Disjoint (Metric.closedBall γ.vertices[i.1] (radius i))
        (Metric.closedBall γ.vertices[j.1] (radius j))
  adjacent_radii_sum_lt :
    ∀ ⦃j : ℕ⦄, (hj : j + 1 < γ.vertices.length) →
      radius ⟨j, Nat.lt_of_succ_lt hj⟩ + radius ⟨j + 1, hj⟩ <
        dist γ.vertices[j] γ.vertices[j + 1]
  nonincident_segment_disjoint :
    ∀ ⦃i : Fin γ.vertices.length⦄ ⦃j : ℕ⦄,
      (hj : j + 1 < γ.vertices.length) →
        i.1 ≠ j → i.1 ≠ j + 1 →
          Disjoint (Metric.closedBall γ.vertices[i.1] (radius i))
            (segment ℝ γ.vertices[j] γ.vertices[j + 1])
