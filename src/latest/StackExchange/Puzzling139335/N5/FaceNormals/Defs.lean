import StackExchange.Puzzling139335.Definitions
import Mathlib.Tactic

/-!
# The remaining normal directions for two-point support faces
-/

namespace Puzzling139335.N5

/-- The three closed families left after the open normal cones at the three
distinguished source points have been excluded. -/
def AllowedNormal (c s nx ny : ℝ) : Prop :=
  (nx = 0 ∧ ny = -1) ∨
  (0 < nx ∧ 0 ≤ ny ∧ c * ny ≤ s * nx) ∨
  (nx < 0 ∧ 0 < ny ∧ c * nx + s * ny ≤ 0 ∧ 0 ≤ nx + ny)

/-- The normal has a supporting level attained at two distinct points of
the set.  The set itself need not be convex and need not contain the segment
between those two points. -/
def HasTwoPointSupport (P : Set Plane) (nx ny : ℝ) : Prop :=
  ∃ m : ℝ, ∃ X Y : Plane,
    X ∈ P ∧ Y ∈ P ∧ X ≠ Y ∧
    (∀ p ∈ P, nx * p 0 + ny * p 1 ≤ m) ∧
    nx * X 0 + ny * X 1 = m ∧ nx * Y 0 + ny * Y 1 = m

end Puzzling139335.N5
