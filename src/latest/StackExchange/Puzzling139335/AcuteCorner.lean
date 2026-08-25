import StackExchange.Puzzling139335.AcuteCorner.Cone
import StackExchange.Puzzling139335.AcuteCorner.VisualAngle
import StackExchange.Puzzling139335.SquareGeometry

/-!
# A two-corner tile has no additional forty-five-degree support point

A support point is defined by actual containment of the set in an affine
isometric image of the explicit cone `0 ≤ y ≤ x`. The argument first proves
that a point seeing an adjacent square-side pair inside such a cone is a
square corner. The dissection's proved diameter obstruction then excludes
the other two corners. No hull-angle predicate or polygonal hypothesis is
assumed.
-/

open Set

namespace Puzzling139335.AcuteCorner

private theorem cyclic_corner_cases (j k : Fin 4) :
    k = j ∨ k = j + 1 ∨ k = j + 2 ∨ k = (j + 1) + 2 := by
  fin_cases j <;> fin_cases k <;> decide

private theorem distinct_corner_cases (j k : Fin 4) (hne : j ≠ k) :
    k = j + 1 ∨ j = k + 1 ∨ k = j + 2 := by
  rcases cyclic_corner_cases j k with h | h | h | h
  · exact (hne h.symm).elim
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · right
    left
    rw [h]
    fin_cases j <;> decide

end Puzzling139335.AcuteCorner

namespace Puzzling139335

open AcuteCorner

namespace SquareDissection

/-- An actual member supporting a two-adjacent-corner piece in a forty-five-degree
cone must be one of those two corners. -/
theorem support45_eq_of_adjacent_corners
    (d : SquareDissection) (hc : d.HasProtectedCenter) (i j : Fin 4)
    (hj : corner j ∈ d.piece i) (hj1 : corner (j + 1) ∈ d.piece i)
    {v : Plane} (hv : v ∈ d.piece i) (hsupport : Supports45 (d.piece i) v) :
    v = corner j ∨ v = corner (j + 1) := by
  obtain ⟨k, hvk⟩ := corner_of_adjacent_pair_bound (d.piece_subset i hv) j
    (hsupport.pair_bound hj hj1)
  have hk : corner k ∈ d.piece i := hvk ▸ hv
  rcases AcuteCorner.cyclic_corner_cases j k with h0 | h1 | h2 | h3
  · exact Or.inl (hvk.trans (congrArg corner h0))
  · exact Or.inr (hvk.trans (congrArg corner h1))
  · exact (d.no_opposite_corners hc i j ⟨hj, h2 ▸ hk⟩).elim
  · exact (d.no_opposite_corners hc i (j + 1) ⟨hj1, h3 ▸ hk⟩).elim

/-- The actual two-corner exclusion, with no adjacency hypothesis needed:
opposite pairs are already impossible in a protected-center dissection. -/
theorem support45_eq_of_two_corners
    (d : SquareDissection) (hc : d.HasProtectedCenter) (i j k : Fin 4)
    (hjk : j ≠ k) (hj : corner j ∈ d.piece i) (hk : corner k ∈ d.piece i)
    {v : Plane} (hv : v ∈ d.piece i) (hsupport : Supports45 (d.piece i) v) :
    v = corner j ∨ v = corner k := by
  rcases AcuteCorner.distinct_corner_cases j k hjk with hnext | hprev | hopp
  · subst k
    exact d.support45_eq_of_adjacent_corners hc i j hj hk hv hsupport
  · subst j
    exact (d.support45_eq_of_adjacent_corners hc i k hk hj hv hsupport).symm
  · exact (d.no_opposite_corners hc i j ⟨hj, hopp ▸ hk⟩).elim

/-- The same statement for points known to be square corners, without
requiring their corner indices as theorem arguments. -/
theorem support45_eq_of_corner_points
    (d : SquareDissection) (hc : d.HasProtectedCenter) (i : Fin 4)
    {a b v : Plane} (ha_corner : a ∈ range corner) (hb_corner : b ∈ range corner)
    (hab : a ≠ b) (ha : a ∈ d.piece i) (hb : b ∈ d.piece i)
    (hv : v ∈ d.piece i) (hsupport : Supports45 (d.piece i) v) :
    v = a ∨ v = b := by
  obtain ⟨j, rfl⟩ := ha_corner
  obtain ⟨k, rfl⟩ := hb_corner
  have hjk : j ≠ k := by
    intro h
    exact hab (congrArg corner h)
  exact d.support45_eq_of_two_corners hc i j k hjk ha hb hv hsupport

/-- Pullback to any actual prototype placement: a forty-five-degree support
point must be an intrinsic endpoint of every two-corner placement. -/
theorem support45_preimage_eq_of_two_corners
    (d : SquareDissection) (hc : d.HasProtectedCenter) (i j k : Fin 4)
    (hjk : j ≠ k) (hj : corner j ∈ d.piece i) (hk : corner k ∈ d.piece i)
    {P : Set Plane} {v : Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' P = d.piece i) (hv : v ∈ P) (hsupport : Supports45 P v) :
    v = e.symm (corner j) ∨ v = e.symm (corner k) := by
  have hev : e v ∈ d.piece i := he ▸ mem_image_of_mem e hv
  have hesupport : Supports45 (d.piece i) (e v) := by
    simpa only [he] using hsupport.image e
  rcases d.support45_eq_of_two_corners hc i j k hjk hj hk hev hesupport with h | h
  · exact Or.inl (by simpa using congrArg e.symm h)
  · exact Or.inr (by simpa using congrArg e.symm h)

end SquareDissection

end Puzzling139335
