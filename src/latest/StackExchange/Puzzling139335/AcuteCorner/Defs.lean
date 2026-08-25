import StackExchange.Puzzling139335.Definitions

/-!
# An explicit forty-five-degree supporting cone

The support predicate is geometric containment after a genuine affine
Euclidean isometry. It is not an assumed or undefined hull-angle predicate.
-/

open Set

namespace Puzzling139335.AcuteCorner

/-- The closed cone between the positive horizontal ray and the positive diagonal ray. -/
def cone45 : Set Plane := {p | 0 ≤ p 1 ∧ p 1 ≤ p 0}

/-- The whole set is supported at a point inside a Euclidean cone of angle at most 45 degrees. -/
def Supports45 (P : Set Plane) (v : Plane) : Prop :=
  ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, e v = 0 ∧ e '' P ⊆ cone45

/-- The coordinate scalar product in the Euclidean plane. -/
def dot (u v : Plane) : ℝ := u 0 * v 0 + u 1 * v 1

/-- The signed two-dimensional determinant. -/
def det (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

end Puzzling139335.AcuteCorner
