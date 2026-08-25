import StackExchange.Puzzling139335.N6.TripleEqualParity.Diameter.Algebra
import StackExchange.Puzzling139335.N6.TripleSectors.GlobalCone

/-!
# The unique diameter pair of the equal-parity quadrilateral

The exact coordinate calculation is applied to the actual support bound
arising from the square fits of the normalized placements.
-/

open Set
open Puzzling139335.N6.TripleSectors

namespace Puzzling139335.N6.TripleEqualParity

theorem circle_deficit_nonneg {p : Plane} (hp : p ∈ equalParityBound) :
    0 ≤ p 0 - p 0 ^ 2 + t * p 1 - p 1 ^ 2 :=
  circle_deficit_nonneg_of_bounds hp

theorem dist_sq_le_diagonal {p q : Plane}
    (hp : p ∈ equalParityBound) (hq : q ∈ equalParityBound) :
    dist p q ^ 2 ≤ 1 + t ^ 2 :=
  dist_sq_le_diagonal_of_bounds hp hq

theorem diameter_equality_coordinates {p q : Plane}
    (hp : p ∈ equalParityBound) (hq : q ∈ equalParityBound)
    (hd : dist p q ^ 2 = 1 + t ^ 2) :
    p 0 + q 0 = 1 ∧ p 1 + q 1 = t ∧
      p 0 - p 0 ^ 2 + t * p 1 - p 1 ^ 2 = 0 :=
  diameter_equality_coordinates_of_bounds hp hq hd

theorem second_eq_zero_of_first_eq_zero {p : Plane}
    (hp : p ∈ equalParityBound) (hx : p 0 = 0) : p 1 = 0 :=
  second_eq_zero_of_first_eq_zero_of_bounds hp hx

/-- The unique pair at maximal distance consists of the two named
endpoints, in either order. -/
theorem endpoints_of_dist_sq_eq_diagonal {p q : Plane}
    (hp : p ∈ equalParityBound) (hq : q ∈ equalParityBound)
    (hd : dist p q ^ 2 = 1 + t ^ 2) :
    (p = 0 ∧ q = diagonalEnd) ∨ (p = diagonalEnd ∧ q = 0) :=
  endpoints_of_dist_sq_eq_diagonal_of_bounds hp hq hd

theorem dist_sq_eq_diagonal_iff {p q : Plane}
    (hp : p ∈ equalParityBound) (hq : q ∈ equalParityBound) :
    dist p q ^ 2 = 1 + t ^ 2 ↔
      (p = 0 ∧ q = diagonalEnd) ∨ (p = diagonalEnd ∧ q = 0) :=
  dist_sq_eq_diagonal_iff_of_bounds hp hq

end Puzzling139335.N6.TripleEqualParity
