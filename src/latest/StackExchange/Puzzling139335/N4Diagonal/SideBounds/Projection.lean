import StackExchange.Puzzling139335.ThreeCorners.Rays

/-!
# Coordinate bounds from a supporting line

A contact with a coordinate axis and a ray endpoint in the nonnegative
quadrant bound the coordinates of the supporting vertex.  The scalar
contradiction at the end combines these support bounds with side coverage.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ThreeCorners

/-- A bottom-axis contact and a backward ray endpoint bound the coordinates
of a vertex supporting the piece to the left of its inward ray. -/
theorem bottom_support_coordinate_bounds {P : Set Plane} {p : Plane}
    {θ t x₀ : ℝ}
    (hquadrant : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1)
    (hbottom : (!₂[x₀, 0] : Plane) ∈ P)
    (hend : p - t • ray θ ∈ P)
    (hsupport : ∀ x ∈ P, 0 ≤ inner ℝ (perpRay θ) (x - p))
    (hsin : 0 < Real.sin θ) (hcos : 0 ≤ Real.cos θ) :
    x₀ + t * Real.cos θ ≤ p 0 ∧ t * Real.sin θ ≤ p 1 := by
  have hy : t * Real.sin θ ≤ p 1 := by
    have h := (hquadrant _ hend).2
    simp [ray] at h
    linarith
  have hs : Real.sin θ * x₀ ≤ Real.sin θ * p 0 - Real.cos θ * p 1 := by
    have h := hsupport _ hbottom
    simp [Schoenflies.Plane.inner_eq, perpRay] at h
    nlinarith
  refine ⟨?_, hy⟩
  apply (mul_le_mul_iff_right₀ hsin).mp
  nlinarith [mul_le_mul_of_nonneg_left hy hcos]

/-- A left-axis contact and a backward ray endpoint bound the coordinates
of a vertex supporting the piece to the right of its inward ray. -/
theorem left_support_coordinate_bounds {P : Set Plane} {q : Plane}
    {β t y₀ : ℝ}
    (hquadrant : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1)
    (hleft : (!₂[0, y₀] : Plane) ∈ P)
    (hend : q - t • ray β ∈ P)
    (hsupport : ∀ x ∈ P, inner ℝ (perpRay β) (x - q) ≤ 0)
    (hcos : 0 < Real.cos β) (hsin : 0 ≤ Real.sin β) :
    t * Real.cos β ≤ q 0 ∧ y₀ + t * Real.sin β ≤ q 1 := by
  have hx : t * Real.cos β ≤ q 0 := by
    have h := (hquadrant _ hend).1
    simp [ray] at h
    linarith
  have hs : Real.cos β * y₀ ≤ Real.cos β * q 1 - Real.sin β * q 0 := by
    have h := hsupport _ hleft
    simp [Schoenflies.Plane.inner_eq, perpRay] at h
    nlinarith
  refine ⟨hx, ?_⟩
  apply (mul_le_mul_iff_right₀ hcos).mp
  nlinarith [mul_le_mul_of_nonneg_left hx hsin]

/-- Side coverage is incompatible with a strictly interior angular support
at a positive-height vertex in the lower unit triangle. -/
theorem assignmentI_contradiction {x₀ t px py s c : ℝ}
    (hcover : 1 ≤ x₀ + t)
    (hsupport : s * x₀ ≤ s * px - c * py)
    (hend : t * s ≤ py)
    (htriangle : px + py ≤ 1)
    (hs : 0 < s) (hcs : 1 < c + s) (hpy : 0 < py) : False := by
  nlinarith [mul_le_mul_of_nonneg_left hcover hs.le,
    mul_le_mul_of_nonneg_left htriangle hs.le,
    mul_pos (sub_pos.mpr hcs) hpy]

end Puzzling139335.N4Diagonal
