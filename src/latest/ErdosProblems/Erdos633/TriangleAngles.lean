import ErdosProblems.Erdos633.Congruence
import ErdosProblems.Erdos633.Isosceles
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Euclidean angles and sine-rule ratios for nondegenerate triangles

These angles are computed from the actual vertices of `Triangle`. Their
positivity and angle sum follow from its nondegeneracy, rather than being
assumed in an auxiliary angle ledger.
-/

namespace Erdos633

open scoped EuclideanGeometry

noncomputable def Triangle.angleA (P : Triangle) : ℝ := ∠ P.b P.a P.c
noncomputable def Triangle.angleB (P : Triangle) : ℝ := ∠ P.a P.b P.c
noncomputable def Triangle.angleC (P : Triangle) : ℝ := ∠ P.a P.c P.b

@[simp] theorem Triangle.angleA_rotate (P : Triangle) : P.rotate.angleA = P.angleB :=
  EuclideanGeometry.angle_comm _ _ _

@[simp] theorem Triangle.angleB_rotate (P : Triangle) : P.rotate.angleB = P.angleC :=
  EuclideanGeometry.angle_comm _ _ _

@[simp] theorem Triangle.angleC_rotate (P : Triangle) : P.rotate.angleC = P.angleA := rfl

theorem Triangle.not_collinear (P : Triangle) : ¬ Collinear ℝ ({P.a, P.b, P.c} : Set ℂ) :=
  affineIndependent_iff_not_collinear_set.mp P.affineIndependent

theorem Triangle.angleA_pos (P : Triangle) : 0 < P.angleA :=
  EuclideanGeometry.angle_pos_of_not_collinear P.swapAB.not_collinear

theorem Triangle.angleB_pos (P : Triangle) : 0 < P.angleB :=
  EuclideanGeometry.angle_pos_of_not_collinear P.not_collinear

theorem Triangle.angleC_pos (P : Triangle) : 0 < P.angleC :=
  EuclideanGeometry.angle_pos_of_not_collinear P.swapBC.not_collinear

theorem Triangle.angleA_lt_pi (P : Triangle) : P.angleA < Real.pi :=
  EuclideanGeometry.angle_lt_pi_of_not_collinear P.swapAB.not_collinear

theorem Triangle.angleB_lt_pi (P : Triangle) : P.angleB < Real.pi :=
  EuclideanGeometry.angle_lt_pi_of_not_collinear P.not_collinear

theorem Triangle.angleC_lt_pi (P : Triangle) : P.angleC < Real.pi :=
  EuclideanGeometry.angle_lt_pi_of_not_collinear P.swapBC.not_collinear

theorem Triangle.angle_sum (P : Triangle) : P.angleA + P.angleB + P.angleC = Real.pi := by
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi P.c P.a_ne_b.symm
  rw [EuclideanGeometry.angle_comm P.b P.c P.a,
    EuclideanGeometry.angle_comm P.c P.a P.b] at h
  change P.angleB + P.angleC + P.angleA = Real.pi at h
  linarith

theorem Triangle.sin_angleA_pos (P : Triangle) : 0 < Real.sin P.angleA :=
  Real.sin_pos_of_pos_of_lt_pi P.angleA_pos P.angleA_lt_pi

theorem Triangle.sin_angleC_pos (P : Triangle) : 0 < Real.sin P.angleC :=
  Real.sin_pos_of_pos_of_lt_pi P.angleC_pos P.angleC_lt_pi

theorem Triangle.sideB_over_A (P : Triangle) :
    dist P.a P.c = dist P.b P.c * Real.sin P.angleB / Real.sin P.angleA := by
  have hs := ne_of_gt P.sin_angleA_pos
  have h := EuclideanGeometry.law_sin P.a P.b P.c
  rw [EuclideanGeometry.angle_comm P.c P.a P.b, dist_comm P.c P.a] at h
  change Real.sin P.angleB * dist P.b P.c = Real.sin P.angleA * dist P.a P.c at h
  field_simp
  nlinarith

theorem Triangle.sideC_over_A (P : Triangle) :
    dist P.a P.b = dist P.b P.c * Real.sin P.angleC / Real.sin P.angleA := by
  have hs := ne_of_gt P.sin_angleA_pos
  have h := EuclideanGeometry.law_sin P.c P.a P.b
  rw [EuclideanGeometry.angle_comm P.c P.a P.b,
    EuclideanGeometry.angle_comm P.b P.c P.a] at h
  change Real.sin P.angleA * dist P.a P.b = Real.sin P.angleC * dist P.b P.c at h
  field_simp
  nlinarith

theorem Triangle.sideA_over_C (P : Triangle) :
    dist P.b P.c = dist P.a P.b * Real.sin P.angleA / Real.sin P.angleC := by
  have hs := ne_of_gt P.sin_angleC_pos
  have h := EuclideanGeometry.law_sin P.a P.c P.b
  rw [dist_comm P.c P.b, dist_comm P.b P.a] at h
  change Real.sin P.angleC * dist P.b P.c = Real.sin P.angleA * dist P.a P.b at h
  field_simp
  nlinarith

theorem Triangle.sideB_over_C (P : Triangle) :
    dist P.a P.c = dist P.a P.b * Real.sin P.angleB / Real.sin P.angleC := by
  have hs := ne_of_gt P.sin_angleC_pos
  have h := EuclideanGeometry.law_sin P.b P.c P.a
  rw [EuclideanGeometry.angle_comm P.b P.c P.a, dist_comm P.c P.a] at h
  change Real.sin P.angleC * dist P.a P.c = Real.sin P.angleB * dist P.a P.b at h
  field_simp
  nlinarith

theorem Triangle.admitsNonsquareTiling_of_equal_angleA_angleB (P : Triangle)
    (h : P.angleA = P.angleB) : AdmitsNonsquareTiling P := by
  have hs := ne_of_gt P.sin_angleA_pos
  have hside := P.sideB_over_A
  rw [← h] at hside
  have hlegs : dist P.c P.a = dist P.c P.b := by
    rw [dist_comm P.c P.a, dist_comm P.c P.b, hside]
    field_simp
  exact P.admitsNonsquareTiling_of_isosceles (Or.inr (Or.inr hlegs))

/-- Equal Euclidean angles, in any pair of positions, give an actual nonsquare tiling. -/
theorem Triangle.admitsNonsquareTiling_of_equal_angles (P : Triangle)
    (h : P.angleA = P.angleB ∨ P.angleB = P.angleC ∨ P.angleC = P.angleA) :
    AdmitsNonsquareTiling P := by
  rcases h with h | h | h
  · exact P.admitsNonsquareTiling_of_equal_angleA_angleB h
  · have hrot := P.rotate.admitsNonsquareTiling_of_equal_angleA_angleB
      (by simpa only [Triangle.angleA_rotate, Triangle.angleB_rotate] using h)
    exact admitsNonsquareTiling_of_carrier_eq hrot P.rotate_carrier
  · have hrot := P.rotate.rotate.admitsNonsquareTiling_of_equal_angleA_angleB
      (by simpa only [Triangle.angleA_rotate, Triangle.angleB_rotate,
        Triangle.angleC_rotate] using h)
    exact admitsNonsquareTiling_of_carrier_eq hrot
      (P.rotate.rotate_carrier.trans P.rotate_carrier)

end Erdos633
