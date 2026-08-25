import StackExchange.Puzzling139335.N4TwoOneOne.AlignedOutgoing.Boundary
import StackExchange.Puzzling139335.N4TwoOneOne.AlignedOutgoing.Rectangles
import StackExchange.Puzzling139335.N4TwoOneOne.AlignedOutgoing.Parameters
import StackExchange.Puzzling139335.N4TwoOneOne.AlignedOutgoing.Incoming

/-!
# Excluding the aligned outgoing placements

The fourth piece cannot be a one-third inward translation of either
reflected singleton. Actual square coverage forces open rectangles into
the singleton and the fourth piece. The image of the source's bottom
support line then meets one of these forced interiors.

The argument uses only the actual bottom corner, not an assumed bottom
boundary segment or any convex-hull/contact classification.
-/

open Set

namespace Puzzling139335.N4TwoOneOne.AlignedOutgoing

noncomputable section

variable {d : SquareDissection} {θ u v : ℝ}

/-- The right singleton cannot be translated left by one third to form
the fourth piece. All forced-interior facts are proved from coverage. -/
theorem right_placement_impossible (h : SourceData d θ u v)
    (hθ : θ < Real.pi / 2) (hv : 0 < v)
    (hD : horizontalShift (-(1 / 3 : ℝ)) '' d.piece 1 = d.piece 3) : False := by
  let H : ℝ := u * Real.sin θ + v * Real.cos θ
  have hH0 : 0 ≤ H := height_nonneg h
  have hheight : ∀ p ∈ d.piece 0, p 1 ≤ H := fun _ hp => h.height_bound hp
  have hstart : H < 1 - v := start_above_height h
  have hc : 0 < Real.cos θ := cos_pos h hθ
  have hu : 0 < u := hc.trans_le h.cos_le_u
  let A : Plane := rightMap θ u v !₂[0, 0]
  have hAx : A 0 = 1 - u := by simp [A, rightMap, eCoord]
  have hAy : A 1 = 1 - v := by simp [A, rightMap, fCoord]
  have hAmem : A ∈ d.piece 1 := by
    rw [← h.right_image]
    exact ⟨!₂[0, 0], by simpa [corner] using h.bottom_left, rfl⟩
  have hAnot : A ∉ interior (d.piece 1) := by
    rw [← h.right_image]
    exact right_base_not_mem_interior (d.piece_subset 0) θ u v 0
  have hAyI : A 1 ∈ Ioo H 1 := by rw [hAy]; exact ⟨hstart, by linarith⟩
  have hAxhalf : (1 / 2 : ℝ) ≤ A 0 := by rw [hAx]; linarith [h.u_le_half]
  have hAxone : A 0 < 1 := by rw [hAx]; linarith
  have hAxthird : A 0 = 2 / 3 := by
    rcases lt_trichotomy (A 0) (2 / 3 : ℝ) with hlt | heq | hgt
    · have hmid : A ∈ openRectangle (1 / 3) (2 / 3) H :=
        ⟨⟨by linarith, hlt⟩, hAyI⟩
      have hi := middle_rectangle_forced_from_right h hD hheight hH0 hmid
      exact (d.not_mem_other_piece (by decide : (3 : Fin 4) ≠ 1) hi hAmem).elim
    · exact heq
    · exact (hAnot (right_rectangle_forced h hD hheight hH0
        ⟨⟨hgt, hAxone⟩, hAyI⟩)).elim
  have hthird : 1 - u = 2 / 3 := hAx.symm.trans hAxthird
  obtain ⟨t, _, _, hct0, hct, hyt0, hyt1⟩ :=
    exists_short_step hH0 hstart hv hc h.cos_le_half h.sin_nonneg (Real.sin_le_one θ)
  have hstep : rightMap θ u v !₂[t, 0] ∈ openRectangle (2 / 3) 1 H := by
    change ((2 / 3 : ℝ) < 1 - u + (Real.cos θ * t + Real.sin θ * 0) ∧
        1 - u + (Real.cos θ * t + Real.sin θ * 0) < 1) ∧
      H < 1 - v + (-Real.sin θ * t + Real.cos θ * 0) ∧
        1 - v + (-Real.sin θ * t + Real.cos θ * 0) < 1
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hi := right_rectangle_forced h hD hheight hH0 hstep
  rw [← h.right_image] at hi
  exact right_base_not_mem_interior (d.piece_subset 0) θ u v t hi

/-- The reflected placement, translating the left singleton right by one
third, is excluded by the same actual-strip argument. -/
theorem left_placement_impossible (h : SourceData d θ u v)
    (hθ : θ < Real.pi / 2) (hv : 0 < v)
    (hD : horizontalShift (1 / 3 : ℝ) '' d.piece 2 = d.piece 3) : False := by
  let H : ℝ := u * Real.sin θ + v * Real.cos θ
  have hH0 : 0 ≤ H := height_nonneg h
  have hheight : ∀ p ∈ d.piece 0, p 1 ≤ H := fun _ hp => h.height_bound hp
  have hstart : H < 1 - v := start_above_height h
  have hc : 0 < Real.cos θ := cos_pos h hθ
  have hu : 0 < u := hc.trans_le h.cos_le_u
  let A : Plane := leftMap θ u v !₂[0, 0]
  have hAx : A 0 = u := by simp [A, leftMap, eCoord]
  have hAy : A 1 = 1 - v := by simp [A, leftMap, fCoord]
  have hAmem : A ∈ d.piece 2 := by
    rw [← h.left_image]
    exact ⟨!₂[0, 0], by simpa [corner] using h.bottom_left, rfl⟩
  have hAnot : A ∉ interior (d.piece 2) := by
    rw [← h.left_image]
    exact left_base_not_mem_interior (d.piece_subset 0) θ u v 0
  have hAyI : A 1 ∈ Ioo H 1 := by rw [hAy]; exact ⟨hstart, by linarith⟩
  have hAxhalf : A 0 ≤ (1 / 2 : ℝ) := by rw [hAx]; exact h.u_le_half
  have hAxzero : 0 < A 0 := by rw [hAx]; exact hu
  have hAxthird : A 0 = 1 / 3 := by
    rcases lt_trichotomy (A 0) (1 / 3 : ℝ) with hlt | heq | hgt
    · exact (hAnot (left_rectangle_forced h hD hheight hH0
        ⟨⟨hAxzero, hlt⟩, hAyI⟩)).elim
    · exact heq
    · have hmid : A ∈ openRectangle (1 / 3) (2 / 3) H :=
        ⟨⟨hgt, by linarith⟩, hAyI⟩
      have hi := middle_rectangle_forced_from_left h hD hheight hH0 hmid
      exact (d.not_mem_other_piece (by decide : (3 : Fin 4) ≠ 2) hi hAmem).elim
  have hthird : u = 1 / 3 := hAx.symm.trans hAxthird
  obtain ⟨t, _, _, hct0, hct, hyt0, hyt1⟩ :=
    exists_short_step hH0 hstart hv hc h.cos_le_half h.sin_nonneg (Real.sin_le_one θ)
  have hstep : leftMap θ u v !₂[t, 0] ∈ openRectangle 0 (1 / 3) H := by
    change ((0 : ℝ) < u - (Real.cos θ * t + Real.sin θ * 0) ∧
        u - (Real.cos θ * t + Real.sin θ * 0) < 1 / 3) ∧
      H < 1 - v + (-Real.sin θ * t + Real.cos θ * 0) ∧
        1 - v + (-Real.sin θ * t + Real.cos θ * 0) < 1
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hi := left_rectangle_forced h hD hheight hH0 hstep
  rw [← h.left_image] at hi
  exact left_base_not_mem_interior (d.piece_subset 0) θ u v t hi

/-- Neither outgoing-aligned placement is compatible with the dissection. -/
theorem no_aligned_outgoing (h : SourceData d θ u v)
    (hθ : θ < Real.pi / 2) (hv : 0 < v)
    (hD : horizontalShift (-(1 / 3 : ℝ)) '' d.piece 1 = d.piece 3 ∨
      horizontalShift (1 / 3 : ℝ) '' d.piece 2 = d.piece 3) : False := by
  rcases hD with hD | hD
  · exact right_placement_impossible h hθ hv hD
  · exact left_placement_impossible h hθ hv hD

end

end Puzzling139335.N4TwoOneOne.AlignedOutgoing
