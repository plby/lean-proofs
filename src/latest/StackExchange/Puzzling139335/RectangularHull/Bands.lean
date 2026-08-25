import StackExchange.Puzzling139335.RectangularHull.Interlacing

/-!
# Actual side contacts constrain rectangular hull bands

These are direct consequences of Jordan interlacing for the pieces of a
square dissection. The hypotheses are memberships of actual points, not
memberships merely in an enclosing box.
-/

open Set

namespace Puzzling139335.RectangularHull

/-- The two bottom-corner pieces cannot have overlapping proper spans
along the bottom side. -/
theorem bottom_corner_contact_order (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) {w v : ℝ}
    (hv : 0 < v) (hw : w < 1)
    (hBL : Schoenflies.Plane.mk 0 0 ∈ d.piece i)
    (hwP : Schoenflies.Plane.mk w 0 ∈ d.piece i)
    (hvQ : Schoenflies.Plane.mk v 0 ∈ d.piece j)
    (hBR : Schoenflies.Plane.mk 1 0 ∈ d.piece j) : w ≤ v := by
  by_contra h
  exact squareDissection_bottom_side_interlacing_impossible d hij
    (by norm_num : (0 : ℝ) ≤ 0) hv (lt_of_not_ge h) hw (by norm_num)
    hBL hwP hvQ hBR

/-- Proper rectangular hull spans longer than half a side cannot be
anchored at both ends of that side by different pieces. -/
theorem two_long_bottom_spans_impossible (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) {w u : ℝ}
    (hw : (1 / 2 : ℝ) < w) (hu : (1 / 2 : ℝ) < u)
    (hw1 : w < 1) (hu1 : u < 1)
    (hBL : Schoenflies.Plane.mk 0 0 ∈ d.piece i)
    (hwP : Schoenflies.Plane.mk w 0 ∈ d.piece i)
    (huQ : Schoenflies.Plane.mk (1 - u) 0 ∈ d.piece j)
    (hBR : Schoenflies.Plane.mk 1 0 ∈ d.piece j) : False := by
  have h := bottom_corner_contact_order d hij (by linarith) hw1 hBL hwP huQ hBR
  linarith

/-- Two opposite anchored rectangular hulls have height at most one half.
The upper contacts used here are actual rectangle vertices in the pieces. -/
theorem opposite_band_height_le_half (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) {h : ℝ} (hh1 : h ≤ 1)
    (hBR : Schoenflies.Plane.mk 1 0 ∈ d.piece i)
    (hP : Schoenflies.Plane.mk 0 h ∈ d.piece i)
    (hTR : Schoenflies.Plane.mk 1 1 ∈ d.piece j)
    (hQ : Schoenflies.Plane.mk 0 (1 - h) ∈ d.piece j) : h ≤ 1 / 2 := by
  by_contra hlarge
  exact left_right_interlacing_impossible (d.jordan j) (d.jordan i)
    (d.piece_subset j) (d.piece_subset i) (d.disjoint_interiors hij.symm)
    (by linarith : (0 : ℝ) ≤ 1 - h) (by linarith : 1 - h < h) hh1
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) (by norm_num)
    hQ hTR hP hBR

end Puzzling139335.RectangularHull
