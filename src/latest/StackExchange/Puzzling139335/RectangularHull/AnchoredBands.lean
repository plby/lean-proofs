import StackExchange.Puzzling139335.RectangularHull.AxisBox

/-!
# Cornered rectangular hulls with a unit edge are side bands

The four indices are bottom, right, top, and left.  A unit coordinate span
inside the square has endpoints zero and one; the square corner then anchors
the other coordinate interval at one of its two endpoints.
-/

namespace Puzzling139335.RectangularHull

open Set

def sideBand (h : ℝ) (s : Fin 4) : Set Plane :=
  ![closedAxisBox 0 1 0 h, closedAxisBox (1 - h) 1 0 1,
    closedAxisBox 0 1 (1 - h) 1, closedAxisBox 0 h 0 1] s

@[simp] theorem sideBand_zero (h : ℝ) : sideBand h 0 = closedAxisBox 0 1 0 h := rfl

@[simp] theorem sideBand_one (h : ℝ) : sideBand h 1 = closedAxisBox (1 - h) 1 0 1 := rfl

@[simp] theorem sideBand_two (h : ℝ) : sideBand h 2 = closedAxisBox 0 1 (1 - h) 1 := rfl

@[simp] theorem sideBand_three (h : ℝ) : sideBand h 3 = closedAxisBox 0 h 0 1 := rfl

/-- The scalar box classification, with either assignment of the unit side. -/
theorem closedAxisBox_eq_sideBand_of_corner {l r b t h : ℝ}
    (hl0 : 0 ≤ l) (hr1 : r ≤ 1) (hb0 : 0 ≤ b) (ht1 : t ≤ 1)
    (hshape : (r - l = 1 ∧ t - b = h) ∨ (r - l = h ∧ t - b = 1))
    {j : Fin 4} (hj : corner j ∈ closedAxisBox l r b t) :
    ∃ s : Fin 4, closedAxisBox l r b t = sideBand h s := by
  rcases hshape with ⟨hw, hh⟩ | ⟨hw, hh⟩
  · have hl : l = 0 := by linarith only [hl0, hr1, hw]
    have hr : r = 1 := by linarith only [hl0, hr1, hw]
    have hy : corner j 1 = 0 ∨ corner j 1 = 1 := by
      by_cases htop : j = 2 ∨ j = 3 <;> simp [corner, htop]
    rcases hy with hy | hy
    · have hcorner : b ≤ 0 := by simpa only [hy] using hj.2.1
      have hb : b = 0 := by linarith only [hb0, hcorner]
      have ht : t = h := by linarith only [hh, hb]
      refine ⟨0, ?_⟩
      rw [hl, hr, hb, ht]
      rfl
    · have hcorner : 1 ≤ t := by simpa only [hy] using hj.2.2
      have ht : t = 1 := by linarith only [ht1, hcorner]
      have hb : b = 1 - h := by linarith only [hh, ht]
      refine ⟨2, ?_⟩
      rw [hl, hr, hb, ht]
      rfl
  · have hb : b = 0 := by linarith only [hb0, ht1, hh]
    have ht : t = 1 := by linarith only [hb0, ht1, hh]
    have hx : corner j 0 = 0 ∨ corner j 0 = 1 := by
      by_cases hright : j = 1 ∨ j = 2 <;> simp [corner, hright]
    rcases hx with hx | hx
    · have hcorner : l ≤ 0 := by simpa only [hx] using hj.1.1
      have hl : l = 0 := by linarith only [hl0, hcorner]
      have hr : r = h := by linarith only [hw, hl]
      refine ⟨3, ?_⟩
      rw [hl, hr, hb, ht]
      rfl
    · have hcorner : 1 ≤ r := by simpa only [hx] using hj.1.2
      have hr : r = 1 := by linarith only [hr1, hcorner]
      have hl : l = 1 - h := by linarith only [hw, hr]
      refine ⟨1, ?_⟩
      rw [hl, hr, hb, ht]
      rfl

/-- A cornered rectangle contained in the square with side lengths `1,h`,
in either order, is one of the four anchored bands. -/
theorem Frame.exists_sideBand_of_unit_edge (R : Frame) {h : ℝ}
    (hS : R.carrier ⊆ unitSquare)
    (hlengths : (‖R.first‖ = 1 ∧ ‖R.second‖ = h) ∨
      (‖R.first‖ = h ∧ ‖R.second‖ = 1))
    {j : Fin 4} (hj : corner j ∈ R.carrier) :
    ∃ s : Fin 4, R.carrier = sideBand h s := by
  have hAxis := R.axisAligned_of_corner_mem hS hj
  have hbox := R.carrier_eq_closedAxisBox hAxis
  have ho := hS (R.vertices_subset_carrier R.origin_mem_vertices)
  have hd := hS (R.vertices_subset_carrier R.both_mem_vertices)
  have hbounds : 0 ≤ R.boxLeft ∧ R.boxRight ≤ 1 ∧
      0 ≤ R.boxBottom ∧ R.boxTop ≤ 1 :=
    ⟨le_min ho.1.1 hd.1.1, max_le ho.1.2 hd.1.2,
      le_min ho.2.1 hd.2.1, max_le ho.2.2 hd.2.2⟩
  have hshape :
      (R.boxRight - R.boxLeft = 1 ∧ R.boxTop - R.boxBottom = h) ∨
        (R.boxRight - R.boxLeft = h ∧ R.boxTop - R.boxBottom = 1) := by
    rcases hlengths with ⟨hf, hs⟩ | ⟨hf, hs⟩
    · simpa only [hf, hs] using R.axisBox_side_lengths hAxis
    · simpa only [hf, hs, or_comm] using R.axisBox_side_lengths hAxis
  have hjbox : corner j ∈ closedAxisBox R.boxLeft R.boxRight R.boxBottom R.boxTop := by
    rwa [← hbox]
  obtain ⟨s, hs⟩ := closedAxisBox_eq_sideBand_of_corner hbounds.1 hbounds.2.1
    hbounds.2.2.1 hbounds.2.2.2 hshape hjbox
  exact ⟨s, hbox.trans hs⟩

/-- The fixed-order version used after normalizing the unit edge. -/
theorem Frame.exists_sideBand_of_corner (R : Frame) {h : ℝ}
    (hS : R.carrier ⊆ unitSquare) (hfirst : ‖R.first‖ = 1) (hsecond : ‖R.second‖ = h)
    {j : Fin 4} (hj : corner j ∈ R.carrier) :
    ∃ s : Fin 4, R.carrier = sideBand h s :=
  R.exists_sideBand_of_unit_edge hS (Or.inl ⟨hfirst, hsecond⟩) hj

end Puzzling139335.RectangularHull
