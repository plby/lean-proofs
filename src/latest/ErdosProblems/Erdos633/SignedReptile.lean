import ErdosProblems.Erdos633.ReptileEigenvalues
import ErdosProblems.Erdos633.CharacterBoundary

/-!
# A direction character forces a square reptile count

The signed boundary identity is extracted from the actual tiling. If pi has
integer coordinates in two independent reference angles and a character sends
those coordinates to minus one, the positive similarity scale is an integer.
-/

namespace Erdos633

open scoped EuclideanGeometry

theorem strict_dist_triangle_of_angle_lt_pi (a b c : ℂ)
    (hab : a ≠ b) (hcb : c ≠ b) (hangle : ∠ a b c < Real.pi) :
    dist a c < dist a b + dist c b := by
  have hle := dist_triangle a b c
  rw [dist_comm b c] at hle
  apply lt_of_le_of_ne hle
  intro heq
  exact (ne_of_lt hangle) ((EuclideanGeometry.dist_eq_add_dist_iff_angle_eq_pi hab hcb).mp heq)

theorem Triangle.sideLength_strict_triangle (R : Triangle) :
    R.sideLength 0 < R.sideLength 1 + R.sideLength 2 ∧
      R.sideLength 1 < R.sideLength 0 + R.sideLength 2 ∧
      R.sideLength 2 < R.sideLength 0 + R.sideLength 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [Triangle.sideLength, Triangle.edgeStart, Triangle.edgeEnd, dist_comm, add_comm] using
      strict_dist_triangle_of_angle_lt_pi R.b R.a R.c R.a_ne_b.symm
        R.swapBC.a_ne_b.symm R.angleA_lt_pi
  · simpa [Triangle.sideLength, Triangle.edgeStart, Triangle.edgeEnd, dist_comm, add_comm] using
      strict_dist_triangle_of_angle_lt_pi R.a R.b R.c R.a_ne_b R.b_ne_c.symm R.angleB_lt_pi
  · simpa [Triangle.sideLength, Triangle.edgeStart, Triangle.edgeEnd, dist_comm, add_comm] using
      strict_dist_triangle_of_angle_lt_pi R.a R.c R.b R.swapBC.a_ne_b R.b_ne_c R.angleC_lt_pi

theorem signedTriangleBoundary_aligned (u v : ℤ) (πc : ℤ × ℤ)
    (hπ : directionSign u v πc = -1) (a b c x : ℝ) :
    signedTriangleBoundary u v πc (0, 1) (πc - (1, 1)) (x * a) (x * b) (x * c) =
      x * (c - directionSign u v (0, 1) * a - directionSign u v (1, 0) * b) := by
  have he : (πc - (0, 1)) + (πc - (πc - (1, 1))) = πc + (1, 0) := by
    apply Prod.ext <;> dsimp <;> ring
  unfold signedTriangleBoundary
  rw [he, directionSign_sub, directionSign_add, hπ]
  ring

theorem CongruentTiling.signed_aligned_reptile_isSquare
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hind : IntegerIndependentAngles R.angleA R.angleB) (πc : ℤ × ℤ)
    (hπ : Real.pi = angleFromCoordinates R.angleA R.angleB πc)
    (u v : ℤ) (hchar : directionSign u v πc = -1)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleB) : IsSquare N := by
  by_contra hN
  obtain ⟨x, hx, hsq, hside, _⟩ := T.aligned_reptile_scale hA hB
  have hBC : P.angleB = angleFromCoordinates R.angleA R.angleB (0, 1) := by
    simpa [angleFromCoordinates] using hB
  have hCC : P.angleC = angleFromCoordinates R.angleA R.angleB (πc - (1, 1)) := by
    dsimp [angleFromCoordinates] at hπ ⊢
    push_cast
    linarith [P.angle_sum]
  have hsign := T.integerBoundarySigns hind πc (0, 1) (πc - (1, 1)) hπ hBC hCC
  obtain ⟨m, hm⟩ := hsign u v hchar
  rw [hside 0, hside 1, hside 2, signedTriangleBoundary_aligned u v πc hchar] at hm
  obtain ⟨ha, hb, hc⟩ := R.sideLength_strict_triangle
  have hfactor := directionSign_factor_ne_zero u v
    (R.sideLength 0) (R.sideLength 1) (R.sideLength 2)
    (R.sideLength_pos 0) (R.sideLength_pos 1) (R.sideLength_pos 2) ha hb hc
  have hxint := mul_right_cancel₀ hfactor hm
  apply not_rational_of_sq_eq_nonsquare N x hN hsq
  rw [hxint]
  exact rationalReals_int m

end Erdos633
