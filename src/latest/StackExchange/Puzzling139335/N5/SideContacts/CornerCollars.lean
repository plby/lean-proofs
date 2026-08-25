import StackExchange.Puzzling139335.N5.Normalized
import StackExchange.Puzzling139335.DissectionTopology
import StackExchange.Puzzling139335.SquareGeometry
import StackExchange.Puzzling139335.DoubleCorner.RotationBoundary

/-!
# Local contacts at the bottom corners in the five-incidence case

Unique ownership gives the bottom piece a positive right-side contact.
At the split corner, the two reflected pieces jointly own a relative
square neighborhood. A short positive step along the diagonal lies inside
their union and, being fixed by reflection, belongs to both pieces.
No protected-center assumption is used.
-/

open Set Metric

namespace Puzzling139335.N5

variable {d : SquareDissection}

theorem Normalized.unique_bottom_right (h : Normalized d) :
    ∀ k, k ≠ 0 → corner 1 ∉ d.piece k :=
  unique_corner_of_count_one d
    (count_one_of_ne_split d h.incidence_count h.split_count (by decide)) h.bottom_right

/-- The bottom piece owns a full relative neighborhood of the unsplit
bottom-right corner. -/
theorem Normalized.bottom_right_relative_neighborhood (h : Normalized d) :
    ∃ ε : ℝ, 0 < ε ∧ ball (corner 1) ε ∩ unitSquare ⊆ d.piece 0 :=
  d.unique_piece_relative_neighborhood 0 h.unique_bottom_right

/-- The positive contact can be chosen strictly between the two right
square corners. -/
theorem Normalized.exists_positive_right_contact_lt_one (h : Normalized d) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ Schoenflies.Plane.mk 1 b ∈ d.piece 0 := by
  obtain ⟨ε, hε, hnear⟩ := h.bottom_right_relative_neighborhood
  let b : ℝ := min (1 / 2) (ε / 2)
  have hb : 0 < b := lt_min (by norm_num) (half_pos hε)
  have hbhalf : b ≤ 1 / 2 := min_le_left _ _
  have hbeps : b ≤ ε / 2 := min_le_right _ _
  have hb1 : b < 1 := by linarith only [hbhalf]
  have hdist : dist (Schoenflies.Plane.mk 1 b) (corner 1) = b := by
    apply (sq_eq_sq₀ dist_nonneg hb.le).mp
    norm_num [plane_dist_sq, Schoenflies.Plane.mk, corner, Fin.ext_iff]
  have hball : Schoenflies.Plane.mk 1 b ∈ ball (corner 1) ε := by
    rw [mem_ball, hdist]
    linarith only [hbeps, hε]
  have hunit : Schoenflies.Plane.mk 1 b ∈ unitSquare := by
    change (0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1) ∧ (0 ≤ b ∧ b ≤ 1)
    exact ⟨⟨zero_le_one, le_rfl⟩, hb.le, hb1.le⟩
  exact ⟨b, hb, hb1, hnear ⟨hball, hunit⟩⟩

theorem Normalized.exists_positive_right_contact (h : Normalized d) :
    ∃ b : ℝ, 0 < b ∧ Schoenflies.Plane.mk 1 b ∈ d.piece 0 := by
  obtain ⟨b, hb, _, hmem⟩ := h.exists_positive_right_contact_lt_one
  exact ⟨b, hb, hmem⟩

/-- The two actual owners of the split corner jointly contain a full
relative square neighborhood of that corner. -/
theorem Normalized.bottom_left_pair_relative_neighborhood (h : Normalized d) :
    ∃ ε : ℝ, 0 < ε ∧
      ball (corner 0) ε ∩ unitSquare ⊆ d.piece 0 ∪ d.piece 1 := by
  have howners := split_membership_iff_of_two_owners d h.split_count
    (by decide : (0 : Fin 4) ≠ 1) h.bottom_left h.left_bottom
  have hnot : corner 0 ∉ d.piece 2 ∪ d.piece 3 := by
    rintro (h2 | h3)
    · rcases (howners 2).mp h2 with h20 | h21
      · exact (by decide : (2 : Fin 4) ≠ 0) h20
      · exact (by decide : (2 : Fin 4) ≠ 1) h21
    · rcases (howners 3).mp h3 with h30 | h31
      · exact (by decide : (3 : Fin 4) ≠ 0) h30
      · exact (by decide : (3 : Fin 4) ≠ 1) h31
  have hopen : IsOpen (d.piece 2 ∪ d.piece 3)ᶜ :=
    ((d.jordan 2).isClosed.union (d.jordan 3).isClosed).isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hnot)
  refine ⟨ε, hε, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := d.exists_piece_mem hx.2
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi
  · exact (hball hx.1 (Or.inl hi)).elim
  · exact (hball hx.1 (Or.inr hi)).elim

/-- A positive diagonal point near the split corner is an actual common
point of the two pieces and an interior point of their union. -/
theorem Normalized.exists_common_diagonal_interior (h : Normalized d) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧
      Schoenflies.Plane.mk a a ∈ interior (d.piece 0 ∪ d.piece 1) ∧
      Schoenflies.Plane.mk a a ∈ d.piece 0 ∩ d.piece 1 := by
  obtain ⟨ε, hε, hnear⟩ := h.bottom_left_pair_relative_neighborhood
  let a : ℝ := min (1 / 4) (ε / 4)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have haquarter : a ≤ 1 / 4 := min_le_left _ _
  have haeps : a ≤ ε / 4 := min_le_right _ _
  have hahalf : a < 1 / 2 := by linarith only [haquarter]
  have ha1 : a < 1 := by linarith only [haquarter]
  have hdist : dist (Schoenflies.Plane.mk a a) (corner 0) < ε := by
    apply (sq_lt_sq₀ dist_nonneg hε.le).mp
    have htwo : 2 * a < ε := by linarith only [haeps, hε]
    have hsq : (2 * a) ^ 2 < ε ^ 2 :=
      (sq_lt_sq₀ (by positivity) hε.le).mpr htwo
    have hdiag : dist (Schoenflies.Plane.mk a a) (corner 0) ^ 2 = 2 * a ^ 2 := by
      norm_num [plane_dist_sq, Schoenflies.Plane.mk, corner, Fin.ext_iff]
      ring
    rw [hdiag]
    nlinarith [sq_nonneg a]
  have hunit : Schoenflies.Plane.mk a a ∈ interior unitSquare := by
    apply DoubleCorner.interior_unitSquare_of_coordinates
    · exact ⟨ha, ha1⟩
    · exact ⟨ha, ha1⟩
  have hopen : IsOpen (ball (corner 0) ε ∩ interior unitSquare) :=
    isOpen_ball.inter isOpen_interior
  have hsub : ball (corner 0) ε ∩ interior unitSquare ⊆ d.piece 0 ∪ d.piece 1 :=
    fun _ hx => hnear ⟨hx.1, interior_subset hx.2⟩
  have hint : Schoenflies.Plane.mk a a ∈ interior (d.piece 0 ∪ d.piece 1) := by
    apply interior_mono hsub
    rw [hopen.interior_eq]
    exact ⟨mem_ball.mpr hdist, hunit⟩
  have hfixed : ReflectionSeparation.diagonal (Schoenflies.Plane.mk a a) =
      Schoenflies.Plane.mk a a := ReflectionSeparation.diagonal_fixed rfl
  refine ⟨a, ha, hahalf, hint, ?_⟩
  rcases interior_subset hint with hp0 | hp1
  · refine ⟨hp0, ?_⟩
    rw [← h.diagonal_image]
    exact ⟨Schoenflies.Plane.mk a a, hp0, hfixed⟩
  · refine ⟨?_, hp1⟩
    obtain ⟨q, hq, hqp⟩ := h.diagonal_image.symm ▸ hp1
    have hqeq : q = Schoenflies.Plane.mk a a := by
      simpa only [ReflectionSeparation.diagonal_involutive, hfixed] using
        congrArg ReflectionSeparation.diagonal hqp
    exact hqeq ▸ hq

end Puzzling139335.N5
