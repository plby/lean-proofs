import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Defs

open Set

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

/-- Unit outward normals carrying an actual supporting segment of length
at least `δ`. The length threshold is uniform across the normal set. -/
def supportingNormalsAtLeast (K : Set Plane) (δ : ℝ) : Set (ℝ × ℝ) :=
  {n | n.1 ^ 2 + n.2 ^ 2 = 1 ∧
    ∃ a b : Plane, SupportsSegment K n.1 n.2 a b ∧ δ ≤ dist a b}

/-- Unit outward normal directions with supporting segments of length
at least one. -/
abbrev unitSupportingNormals (K : Set Plane) : Set (ℝ × ℝ) :=
  supportingNormalsAtLeast K 1

end Puzzling139335.N4MiddleInvolutions.FaceBounds
