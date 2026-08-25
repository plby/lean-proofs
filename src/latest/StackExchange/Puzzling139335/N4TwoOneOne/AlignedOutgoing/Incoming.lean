import StackExchange.Puzzling139335.N4TwoOneOne.SourceBounds

/-!
# The incoming-aligned top placement misses the protected center

Only the actual image equality and the height coordinate of the placement
are used. Nonnegative source coordinates force the entire fourth piece
into the upper half of the square.
-/

open Set

namespace Puzzling139335.N4TwoOneOne.AlignedOutgoing

variable {d : SquareDissection} {θ u v : ℝ} {g : Plane → Plane}

/-- The incoming-aligned height formula forces the fourth piece above
the horizontal square midline. -/
theorem incoming_in_upper_half (h : SourceData d θ u v)
    (hg : g '' d.piece 0 = d.piece 3)
    (hheight : ∀ p, g p 1 = 1 - u + eCoord θ p) :
    d.piece 3 ⊆ {p : Plane | (1 / 2 : ℝ) ≤ p 1} := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := hg.symm ▸ hp
  change (1 / 2 : ℝ) ≤ g q 1
  rw [hheight q]
  have hqS := d.piece_subset 0 hq
  have he : 0 ≤ eCoord θ q :=
    add_nonneg (mul_nonneg h.cos_nonneg hqS.1.1)
      (mul_nonneg h.sin_nonneg hqS.2.1)
  linarith only [he, h.u_le_half]

/-- The upper-half containment excludes an interior square center. -/
theorem center_not_incoming_image (h : SourceData d θ u v)
    (hg : g '' d.piece 0 = d.piece 3)
    (hheight : ∀ p, g p 1 = 1 - u + eCoord θ p) :
    squareCenter ∉ interior (d.piece 3) := by
  apply RectangularHull.center_not_in_interior_upper_half
  intro p hp
  have hpS := d.piece_subset 3 hp
  exact ⟨hpS.1, incoming_in_upper_half h hg hheight hp, hpS.2.2⟩

/-- The incoming-aligned top placement is incompatible with a protected
center in the actual four-piece dissection. -/
theorem incoming_aligned_false (h : SourceData d θ u v)
    (hc : d.HasProtectedCenter) (hg : g '' d.piece 0 = d.piece 3)
    (hheight : ∀ p, g p 1 = 1 - u + eCoord θ p) : False :=
  center_not_incoming_image h hg hheight (h.center_piece_three hc)

end Puzzling139335.N4TwoOneOne.AlignedOutgoing
