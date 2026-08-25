import StackExchange.Puzzling139335.N4OuterPair.Defs
import StackExchange.Puzzling139335.DissectionTopology
import StackExchange.Puzzling139335.SquareGeometry

/-!
# Positive side contacts from unique bottom-corner ownership

The upper outer piece and the two cornerless middle pieces omit both
bottom corners.  Closedness of these other pieces therefore gives a full
relative square neighborhood owned by the bottom piece.  In particular,
both of its vertical side contacts contain a point at positive height.
No protected-center assumption is needed for these local conclusions.
-/

open Set Metric

namespace Puzzling139335.N4OuterPair

/-- A positive vertical step can be chosen inside any prescribed ball
while staying below half the square height. -/
theorem exists_positive_vertical_step (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 2 ∧
      dist (Schoenflies.Plane.mk x t) (Schoenflies.Plane.mk x 0) < ε := by
  let t : ℝ := min (1 / 4) (ε / 2)
  have ht : 0 < t := lt_min (by norm_num) (half_pos hε)
  have htquarter : t ≤ 1 / 4 := min_le_left _ _
  have htepsilon : t ≤ ε / 2 := min_le_right _ _
  have hdist : dist (Schoenflies.Plane.mk x t) (Schoenflies.Plane.mk x 0) = t := by
    apply (sq_eq_sq₀ dist_nonneg ht.le).mp
    simp [plane_dist_sq, Schoenflies.Plane.mk]
  refine ⟨t, ht, ?_, ?_⟩
  · linarith only [htquarter]
  · rw [hdist]
    linarith only [htepsilon, hε]

namespace Configuration

variable {d : SquareDissection}

/-- Each bottom corner belongs to no piece other than the bottom outer
piece.  The upper piece is excluded by its lower height bound. -/
theorem bottom_corner_unique (h : Configuration d) (k : Fin 4)
    (hk : k = 0 ∨ k = 1) :
    ∀ j : Fin 4, j ≠ 0 → corner k ∉ d.piece j := by
  intro j hj hmem
  fin_cases j
  · exact hj rfl
  · have hy := (h.outer_halves.2 hmem).2.1
    have hzero : corner k 1 = 0 := by
      rcases hk with rfl | rfl <;> norm_num [corner, Fin.ext_iff]
    rw [hzero] at hy
    norm_num at hy
  · exact h.middle_cornerless 2 (Or.inl rfl) k hmem
  · exact h.middle_cornerless 3 (Or.inr rfl) k hmem

theorem bottom_left_unique (h : Configuration d) :
    ∀ j : Fin 4, j ≠ 0 → corner 0 ∉ d.piece j :=
  h.bottom_corner_unique 0 (Or.inl rfl)

theorem bottom_right_unique (h : Configuration d) :
    ∀ j : Fin 4, j ≠ 0 → corner 1 ∉ d.piece j :=
  h.bottom_corner_unique 1 (Or.inr rfl)

theorem bottom_left_relative_neighborhood (h : Configuration d) :
    ∃ ε : ℝ, 0 < ε ∧
      ball (Schoenflies.Plane.mk 0 0) ε ∩ unitSquare ⊆ d.piece 0 := by
  simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using
    d.unique_piece_relative_neighborhood 0 h.bottom_left_unique

theorem bottom_right_relative_neighborhood (h : Configuration d) :
    ∃ ε : ℝ, 0 < ε ∧
      ball (Schoenflies.Plane.mk 1 0) ε ∩ unitSquare ⊆ d.piece 0 := by
  simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using
    d.unique_piece_relative_neighborhood 0 h.bottom_right_unique

/-- The bottom piece has an actual point above the left bottom corner. -/
theorem exists_left_leg_point (h : Configuration d) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ Schoenflies.Plane.mk 0 a ∈ d.piece 0 := by
  obtain ⟨ε, hε, hnear⟩ := h.bottom_left_relative_neighborhood
  obtain ⟨a, ha, hah, hdist⟩ := exists_positive_vertical_step 0 hε
  have hunit : Schoenflies.Plane.mk 0 a ∈ unitSquare := by
    change (0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1) ∧ (0 ≤ a ∧ a ≤ 1)
    exact ⟨⟨le_rfl, zero_le_one⟩, ha.le, by linarith only [hah]⟩
  exact ⟨a, ha, hah, hnear ⟨Metric.mem_ball.mpr hdist, hunit⟩⟩

/-- The bottom piece has an actual point above the right bottom corner. -/
theorem exists_right_leg_point (h : Configuration d) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 2 ∧ Schoenflies.Plane.mk 1 b ∈ d.piece 0 := by
  obtain ⟨ε, hε, hnear⟩ := h.bottom_right_relative_neighborhood
  obtain ⟨b, hb, hbh, hdist⟩ := exists_positive_vertical_step 1 hε
  have hunit : Schoenflies.Plane.mk 1 b ∈ unitSquare := by
    change (0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1) ∧ (0 ≤ b ∧ b ≤ 1)
    exact ⟨⟨zero_le_one, le_rfl⟩, hb.le, by linarith only [hbh]⟩
  exact ⟨b, hb, hbh, hnear ⟨Metric.mem_ball.mpr hdist, hunit⟩⟩

/-- The positive-contact conclusion in a uniform side-coordinate form. -/
theorem exists_side_leg_point (h : Configuration d) (x : ℝ) (hx : x = 0 ∨ x = 1) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ Schoenflies.Plane.mk x a ∈ d.piece 0 := by
  rcases hx with rfl | rfl
  · exact h.exists_left_leg_point
  · exact h.exists_right_leg_point

end Configuration

end Puzzling139335.N4OuterPair
