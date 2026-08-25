import StackExchange.Puzzling139335.SquareGeometry
import Mathlib.Analysis.Convex.Basic

/-! Actual supporting-segment certificates for finite face bounds. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

/-- The linear functional with the indicated outward normal. -/
def supportValue (nx ny : ℝ) (p : Plane) : ℝ := nx * p 0 + ny * p 1

/-- Both named endpoints are actual points of `K` on one supporting line.
No perimeter or boundary ordering is part of this certificate. -/
structure SupportsSegment (K : Set Plane) (nx ny : ℝ) (a b : Plane) : Prop where
  left_mem : a ∈ K
  right_mem : b ∈ K
  left_support : ∀ p ∈ K, supportValue nx ny p ≤ supportValue nx ny a
  right_support : ∀ p ∈ K, supportValue nx ny p ≤ supportValue nx ny b

theorem SupportsSegment.level_eq {K : Set Plane} {nx ny : ℝ} {a b : Plane}
    (h : SupportsSegment K nx ny a b) :
    supportValue nx ny a = supportValue nx ny b :=
  le_antisymm (h.right_support a h.left_mem) (h.left_support b h.right_mem)

theorem SupportsSegment.symm {K : Set Plane} {nx ny : ℝ} {a b : Plane}
    (h : SupportsSegment K nx ny a b) : SupportsSegment K nx ny b a :=
  ⟨h.right_mem, h.left_mem, h.right_support, h.left_support⟩

theorem SupportsSegment.segment_subset {K : Set Plane} {nx ny : ℝ} {a b : Plane}
    (h : SupportsSegment K nx ny a b) (hK : Convex ℝ K) : segment ℝ a b ⊆ K :=
  hK.segment_subset h.left_mem h.right_mem

end Puzzling139335.N4MiddleInvolutions.FaceBounds
