import StackExchange.Puzzling139335.N6.TripleEqualParity.Diameter
import StackExchange.Puzzling139335.N6.TripleEqualParity.Scalar

/-!
# An exact metric obstruction to the forced fourth-piece triangle

The argument uses only three actual points of the fourth piece.  Their
preimages under a congruence cannot belong to the source quadrilateral.
No convex hull equality or boundary-area assumption is needed.
-/

open Set
open Puzzling139335.N6.TripleSectors

namespace Puzzling139335.N6.TripleEqualParity

/-- The third vertex cannot have the two required distances to the unique
diameter endpoints while remaining in the source height strip. -/
theorem no_equal_leg_vertex {r : Plane} (hr : r ∈ equalParityBound)
    (hleft : dist r 0 ^ 2 = (1 - t) ^ 2)
    (hright : dist r diagonalEnd ^ 2 = (1 - t) ^ 2) : False := by
  apply no_equal_legs_in_low_strip (x := r 0) t_pos t_lt_one t_quadratic hr.1
    (equalParityBound_second_le_half hr)
  · rw [plane_dist_sq] at hleft
    simpa only [PiLp.zero_apply, sub_zero] using hleft
  · rw [plane_dist_sq] at hright
    simpa only [diagonalEnd_zero, diagonalEnd_one] using hright

/-- No three points in the bounding quadrilateral form the right
isosceles triangle forced into the fourth piece. -/
theorem no_forced_triangle_in_bound {p q r : Plane}
    (hp : p ∈ equalParityBound) (hq : q ∈ equalParityBound)
    (hr : r ∈ equalParityBound)
    (hpq : dist p q ^ 2 = 1 + t ^ 2)
    (hrp : dist r p ^ 2 = (1 - t) ^ 2)
    (hrq : dist r q ^ 2 = (1 - t) ^ 2) : False := by
  rcases endpoints_of_dist_sq_eq_diagonal hp hq hpq with h | h
  · exact no_equal_leg_vertex hr (by simpa only [h.1] using hrp)
      (by simpa only [h.2] using hrq)
  · exact no_equal_leg_vertex hr (by simpa only [h.2] using hrq)
      (by simpa only [h.1] using hrp)

/-- A congruent copy of a subset of the source quadrilateral cannot
contain the three forced square-side points. -/
theorem no_congruent_forced_triangle {P D : Set Plane}
    (hP : P ⊆ equalParityBound) (hPD : Congruent P D)
    (ha : point 1 t ∈ D) (hb : point 1 1 ∈ D) (hc : point t 1 ∈ D) : False := by
  obtain ⟨e, he⟩ := hPD
  have hpre {z : Plane} (hz : z ∈ D) : e.symm z ∈ equalParityBound := by
    rw [← he] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simpa only [e.symm_apply_apply] using hP hw
  apply no_forced_triangle_in_bound (hpre ha) (hpre hc) (hpre hb)
  · rw [e.symm.isometry.dist_eq, plane_dist_sq]
    simp only [point_zero, point_one]
    nlinarith only [t_quadratic]
  · rw [e.symm.isometry.dist_eq, plane_dist_sq]
    simp only [point_zero, point_one]
    ring
  · rw [e.symm.isometry.dist_eq, plane_dist_sq]
    simp only [point_zero, point_one]
    ring

end Puzzling139335.N6.TripleEqualParity
