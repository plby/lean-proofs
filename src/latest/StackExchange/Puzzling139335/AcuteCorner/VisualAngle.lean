import StackExchange.Puzzling139335.AcuteCorner.Defs
import Mathlib

/-!
# Adjacent square corners viewed inside a forty-five-degree cone

An interior or noncorner boundary point of the square cannot see two adjacent square
corners with absolute determinant at most their scalar product. The proof reduces each
of the four adjacent pairs to the same coordinate inequality.
-/

namespace Puzzling139335.AcuteCorner

/-- The sum of the two nonpositive coordinate quadratics can be nonnegative only when
both coordinates are endpoints of the unit interval. -/
theorem coordinate_endpoints_of_quadratic_nonneg {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hquad : 0 ≤ x ^ 2 - x + y ^ 2 - y) :
    (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1) := by
  have hxprod : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  have hyprod : 0 ≤ y * (1 - y) := mul_nonneg hy0 (sub_nonneg.mpr hy1)
  have hxzero : x * (1 - x) = 0 := by nlinarith only [hquad, hxprod, hyprod]
  have hyzero : y * (1 - y) = 0 := by nlinarith only [hquad, hxprod, hyprod]
  constructor
  · rcases mul_eq_zero.mp hxzero with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by linarith only [hx])
  · rcases mul_eq_zero.mp hyzero with hy | hy
    · exact Or.inl hy
    · exact Or.inr (by linarith only [hy])

/-- If a point in the unit square sees an adjacent pair of corners with absolute
determinant at most scalar product, then the point is itself a square corner. -/
theorem corner_of_adjacent_pair_bound {p : Plane} (hp : p ∈ unitSquare) (j : Fin 4)
    (h : |det (corner j - p) (corner (j + 1) - p)| ≤
      dot (corner j - p) (corner (j + 1) - p)) :
    ∃ k : Fin 4, p = corner k := by
  have hdet : det (corner j - p) (corner (j + 1) - p) ≤
      dot (corner j - p) (corner (j + 1) - p) := (le_abs_self _).trans h
  have hquad : 0 ≤ (p 0) ^ 2 - p 0 + (p 1) ^ 2 - p 1 := by
    fin_cases j <;>
      norm_num [dot, det, corner, Fin.ext_iff, Fin.val_add] at hdet <;>
      nlinarith only [hdet]
  rcases hp with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
  rcases coordinate_endpoints_of_quadratic_nonneg hx0 hx1 hy0 hy1 hquad with
    ⟨hx | hx, hy | hy⟩
  · refine ⟨0, ?_⟩
    ext i
    fin_cases i <;> simp [corner, hx, hy]
  · refine ⟨3, ?_⟩
    ext i
    fin_cases i <;> simp [corner, hx, hy]
  · refine ⟨1, ?_⟩
    ext i
    fin_cases i <;> simp [corner, hx, hy]
  · refine ⟨2, ?_⟩
    ext i
    fin_cases i <;> simp [corner, hx, hy]

end Puzzling139335.AcuteCorner
