import StackExchange.Puzzling139335.ReflectionSeparation
import StackExchange.Puzzling139335.BandMass
import StackExchange.Puzzling139335.RectangularHull.FullSide

/-!
# The actual reflected outer pair in the two-double-corner case

Only memberships, an actual reflection identity, and absence of corners from
the two middle pieces are assumed.  Half-plane containment and all subsequent
normalization statements are conclusions.
-/

open Set

namespace Puzzling139335.N4OuterPair

/-- The selected outer pair owns the bottom and top corner pairs. -/
structure Configuration (d : SquareDissection) : Prop where
  bottom_left : corner 0 ∈ d.piece 0
  bottom_right : corner 1 ∈ d.piece 0
  reflected : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1
  middle_cornerless : ∀ i : Fin 4, i = 2 ∨ i = 3 →
    ∀ k : Fin 4, corner k ∉ d.piece i

namespace Configuration

variable {d : SquareDissection}

theorem outer_halves (h : Configuration d) :
    d.piece 0 ⊆ horizontalBand 0 (1 / 2) ∧
      d.piece 1 ⊆ horizontalBand (1 / 2) 1 := by
  have hhalves := d.horizontal_pair_halves_of_bottom_left
    (by norm_num : (0 : Fin 4) ≠ 1) h.reflected h.bottom_left
  constructor
  · intro p hp
    exact ⟨(d.piece_subset 0 hp).1, (d.piece_subset 0 hp).2.1, hhalves.1 hp⟩
  · intro p hp
    exact ⟨(d.piece_subset 1 hp).1, hhalves.2 hp, (d.piece_subset 1 hp).2.2⟩

theorem center_not_outer (h : Configuration d) :
    squareCenter ∉ interior (d.piece 0) ∧ squareCenter ∉ interior (d.piece 1) :=
  ⟨RectangularHull.center_not_in_interior_lower_half h.outer_halves.1,
    RectangularHull.center_not_in_interior_upper_half h.outer_halves.2⟩

theorem center_in_middle (h : Configuration d) (hc : d.HasProtectedCenter) :
    squareCenter ∈ interior (d.piece 2) ∨ squareCenter ∈ interior (d.piece 3) := by
  obtain ⟨i, hi⟩ := hc
  fin_cases i
  · exact (h.center_not_outer.1 hi).elim
  · exact (h.center_not_outer.2 hi).elim
  · exact Or.inl hi
  · exact Or.inr hi

theorem bottom_left_mk (h : Configuration d) :
    Schoenflies.Plane.mk 0 0 ∈ d.piece 0 := by
  simpa [corner, Schoenflies.Plane.mk] using h.bottom_left

theorem bottom_right_mk (h : Configuration d) :
    Schoenflies.Plane.mk 1 0 ∈ d.piece 0 := by
  simpa [corner, Schoenflies.Plane.mk] using h.bottom_right

theorem bottom_side (h : Configuration d) (hc : d.HasProtectedCenter) :
    segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆ d.piece 0 :=
  RectangularHull.lower_outer_hull_contains_bottom_side d hc (by norm_num)
    h.bottom_left_mk h.bottom_right_mk h.outer_halves.1

theorem top_side (h : Configuration d) (hc : d.HasProtectedCenter) :
    segment ℝ (Schoenflies.Plane.mk 0 1) (Schoenflies.Plane.mk 1 1) ⊆ d.piece 1 := by
  have h0 : ReflectionSeparation.horizontal (Schoenflies.Plane.mk 0 0) =
      Schoenflies.Plane.mk 0 1 := by
    ext i
    fin_cases i <;> simp
  have h1 : ReflectionSeparation.horizontal (Schoenflies.Plane.mk 1 0) =
      Schoenflies.Plane.mk 1 1 := by
    ext i
    fin_cases i <;> simp
  have himage : ReflectionSeparation.horizontal ''
      segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) =
      segment ℝ (ReflectionSeparation.horizontal (Schoenflies.Plane.mk 0 0))
        (ReflectionSeparation.horizontal (Schoenflies.Plane.mk 1 0)) :=
    image_segment ℝ ReflectionSeparation.horizontal.toAffineEquiv.toAffineMap _ _
  rw [h0, h1] at himage
  rw [← h.reflected, ← himage]
  exact image_mono (h.bottom_side hc)

end Configuration

end Puzzling139335.N4OuterPair
