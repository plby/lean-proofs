import ErdosProblems.Erdos633.ThirtyTiling
import ErdosProblems.Erdos633.Isosceles
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-!
# Right-triangle cases in geometric angle language

The actual constructions imply the rational-leg and 30-60-90 sufficient
conditions directly for arbitrary triangles, using their Euclidean angles
and distances rather than chosen coordinates.
-/

namespace Erdos633

open scoped EuclideanGeometry

theorem Triangle.pythagorean_of_right (P : Triangle)
    (h : ∠ P.a P.b P.c = Real.pi / 2) :
    Complex.normSq (P.c - P.a) =
      Complex.normSq (P.b - P.a) + Complex.normSq (P.c - P.b) := by
  rw [normSq_sub_eq_dist_sq, normSq_sub_eq_dist_sq, normSq_sub_eq_dist_sq]
  have he := (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two
    P.a P.b P.c).mpr h
  simpa only [pow_two, dist_comm P.c P.b] using he

/-- The full sufficient condition for a right triangle with rational leg ratio. -/
theorem Triangle.admitsNonsquareTiling_of_right_ratio (P : Triangle)
    (hright : ∠ P.a P.b P.c = Real.pi / 2)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hratio : dist P.a P.b / dist P.b P.c = (m : ℝ) / n)
    (hns : ¬ IsSquare (m ^ 2 + n ^ 2)) : AdmitsNonsquareTiling P := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne := ne_of_gt hnR
  have hBC : 0 < dist P.b P.c := dist_pos.mpr P.b_ne_c
  let q := dist P.b P.c / (n : ℝ)
  have hq : 0 < q := div_pos hBC hnR
  have hcross := (div_eq_div_iff (ne_of_gt hBC) hnne).mp hratio
  have hAB : dist P.a P.b = q * m := by
    dsimp [q]
    field_simp
    nlinarith
  have hBCq : dist P.b P.c = q * n := by
    dsimp [q]
    field_simp
  apply P.admitsNonsquareTiling_of_right_sides m n hm hn hns q hq
  · rw [normSq_sub_eq_dist_sq, hAB]
    ring
  · rw [P.pythagorean_of_right hright, normSq_sub_eq_dist_sq, normSq_sub_eq_dist_sq,
      hAB, hBCq]
    ring
  · rw [normSq_sub_eq_dist_sq, hBCq]
    ring

/-- A right triangle with a 60-degree angle admits a nonsquare congruent tiling.
The remaining angle is automatically 30 degrees; no coordinate hypotheses occur. -/
theorem Triangle.admitsNonsquareTiling_of_right_sixty (P : Triangle)
    (hright : ∠ P.b P.a P.c = Real.pi / 2)
    (hsixty : ∠ P.a P.b P.c = Real.pi / 3) : AdmitsNonsquareTiling P := by
  have hright' : ∠ P.c P.a P.b = Real.pi / 2 := by
    rw [EuclideanGeometry.angle_comm]
    exact hright
  have hcos := EuclideanGeometry.cos_angle_mul_dist_of_angle_eq_pi_div_two hright'
  rw [hsixty, Real.cos_pi_div_three, dist_comm P.c P.b, dist_comm P.b P.a] at hcos
  have hhyp : dist P.b P.c = 2 * dist P.a P.b := by linarith
  have hpy := (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two
    P.b P.a P.c).mpr hright
  rw [dist_comm P.b P.a, dist_comm P.c P.a, hhyp] at hpy
  apply P.admitsNonsquareTiling_of_thirty_sides (dist P.a P.b) (dist_pos.mpr P.a_ne_b)
  · exact normSq_sub_eq_dist_sq _ _
  · rw [normSq_sub_eq_dist_sq]
    nlinarith
  · rw [normSq_sub_eq_dist_sq, hhyp]
    ring

end Erdos633
