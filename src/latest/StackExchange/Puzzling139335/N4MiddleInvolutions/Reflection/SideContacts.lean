import StackExchange.Puzzling139335.N4OuterPair.SideGaps

/-!
# Exact side contacts of the actual middle union

A contact of the lower outer piece bounds all contacts of the middle
pieces from below. Horizontal reflection supplies the upper bound.
For a complete initial contact interval, the middle union therefore
meets the side in exactly the complementary closed gap.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

variable {d : SquareDissection}

/-- A middle piece cannot touch a vertical square side below an actual
contact of the lower outer piece on that same side. -/
theorem middle_side_contact_lower_bound
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {x a y : ℝ} (hx : x = 0 ∨ x = 1)
    (htop : Schoenflies.Plane.mk x a ∈ d.piece 0)
    {i : Fin 4} (hi : i = 2 ∨ i = 3)
    (hy : Schoenflies.Plane.mk x y ∈ d.piece i) : a ≤ y := by
  apply le_of_not_gt
  intro hya
  have hy0 : 0 < y := h.middle_y_pos hc hi hy
  have hbase : Schoenflies.Plane.mk x 0 ∈ d.piece 0 := by
    rcases hx with rfl | rfl
    · exact h.bottom_left_mk
    · exact h.bottom_right_mk
  have h0i : (0 : Fin 4) ≠ i := by
    rcases hi with rfl | rfl <;> decide
  have hcap := RectangularHull.vertical_contact_height_bound
    (d.jordan 0) (d.jordan i) (d.piece_subset 0) (d.piece_subset i)
    (d.disjoint_interiors h0i) hx hbase htop
    (fun _ hp => (h.outer_halves.1 hp).2.2) hy0 hya hy
  obtain ⟨p, hp, hpy⟩ := (h.middle_crosses_midline hc hi).2
  exact (not_le_of_gt hpy) (hcap p (interior_subset hp))

private theorem reflected_middle_side_mem
    (h : N4OuterPair.Configuration d) {x y : ℝ}
    (hy : Schoenflies.Plane.mk x y ∈ d.piece 2 ∪ d.piece 3) :
    Schoenflies.Plane.mk x (1 - y) ∈ d.piece 2 ∪ d.piece 3 := by
  have hpoint : ReflectionSeparation.horizontal (Schoenflies.Plane.mk x y) =
      Schoenflies.Plane.mk x (1 - y) := by
    ext i
    fin_cases i <;> simp
  have hmem : ReflectionSeparation.horizontal (Schoenflies.Plane.mk x y) ∈
      d.piece 2 ∪ d.piece 3 :=
    h.middle_union_reflected ▸ mem_image_of_mem ReflectionSeparation.horizontal hy
  simpa only [hpoint] using hmem

/-- Every actual middle contact lies between a lower outer contact and
its horizontal reflection. No hull contact is substituted for membership. -/
theorem middle_side_contact_bounds
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {x a y : ℝ} (hx : x = 0 ∨ x = 1)
    (htop : Schoenflies.Plane.mk x a ∈ d.piece 0)
    (hy : Schoenflies.Plane.mk x y ∈ d.piece 2 ∪ d.piece 3) :
    a ≤ y ∧ y ≤ 1 - a := by
  have hlow (z : ℝ)
      (hz : Schoenflies.Plane.mk x z ∈ d.piece 2 ∪ d.piece 3) : a ≤ z := by
    rcases hz with hz | hz
    · exact middle_side_contact_lower_bound h hc hx htop (Or.inl rfl) hz
    · exact middle_side_contact_lower_bound h hc hx htop (Or.inr rfl) hz
  have hupper := hlow (1 - y) (reflected_middle_side_mem h hy)
  exact ⟨hlow y hy, by linarith only [hupper]⟩

/-- If the lower outer side contact is exactly `[0,a]`, the actual middle
union meets that side in exactly `[a,1-a]`. -/
theorem middle_side_contact_iff
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {x a : ℝ} (hx : x = 0 ∨ x = 1) (ha0 : 0 ≤ a) (haHalf : a < 1 / 2)
    (hcontact : ∀ z : ℝ,
      Schoenflies.Plane.mk x z ∈ d.piece 0 ↔ z ∈ Icc (0 : ℝ) a)
    (y : ℝ) :
    Schoenflies.Plane.mk x y ∈ d.piece 2 ∪ d.piece 3 ↔ y ∈ Icc a (1 - a) := by
  constructor
  · intro hy
    exact middle_side_contact_bounds h hc hx ((hcontact a).mpr ⟨ha0, le_rfl⟩) hy
  · exact h.closed_side_gap_covered hx ha0 haHalf hcontact y

end Puzzling139335.N4MiddleInvolutions.Reflection
