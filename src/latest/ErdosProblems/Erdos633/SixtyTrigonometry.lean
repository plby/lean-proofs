import ErdosProblems.Erdos633.SixtyCriteria
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The fourth-family condition in Euclidean angles

The half-angle parameter gives rational side ratios for a triangle with a
60-degree angle. Together with the W construction this proves the complete
sufficient condition, without an added nonsquare-area assumption.
-/

namespace Erdos633

theorem scaled_half_tangent_formulas (θ q : ℝ) (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hq : q = Real.sqrt 3 * Real.tan (θ / 2)) :
    Real.cos θ = (3 - q ^ 2) / (3 + q ^ 2) ∧
      Real.sqrt 3 * Real.sin θ = 6 * q / (3 + q ^ 2) := by
  have hroot : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ht2 : 3 * Real.tan (θ / 2) ^ 2 = q ^ 2 := by
    calc
      _ = Real.sqrt 3 ^ 2 * Real.tan (θ / 2) ^ 2 := by rw [hroot]
      _ = (Real.sqrt 3 * Real.tan (θ / 2)) ^ 2 := by ring
      _ = q ^ 2 := by rw [← hq]
  have hcos_ne : Real.cos θ ≠ -1 := by
    apply ne_of_gt
    have h := Real.strictAntiOn_cos ⟨hθ0.le, hθπ.le⟩
      ⟨Real.pi_pos.le, le_rfl⟩ hθπ
    simpa only [Real.cos_pi] using h
  have hd : 3 + q ^ 2 ≠ 0 := by positivity
  have ht : 1 + Real.tan (θ / 2) ^ 2 ≠ 0 := by positivity
  have hc := (eq_div_iff ht).mp
    (Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq θ hcos_ne)
  have hs := (eq_div_iff ht).mp
    (Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq θ)
  constructor
  · apply (eq_div_iff hd).mpr
    linear_combination 3 * hc - (Real.cos θ + 1) * ht2
  · apply (eq_div_iff hd).mpr
    linear_combination 3 * Real.sqrt 3 * hs - Real.sqrt 3 * Real.sin θ * ht2 - 6 * hq

theorem sin_over_sin_sixty (θ : ℝ) :
    Real.sin θ / Real.sin (Real.pi / 3) = (2 / 3) * (Real.sqrt 3 * Real.sin θ) := by
  have hroot : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hroot0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [Real.sin_pi_div_three]
  field_simp
  rw [hroot]

theorem sin_sixty_complement_ratio (θ : ℝ) :
    Real.sin (Real.pi - (θ + Real.pi / 3)) / Real.sin (Real.pi / 3) =
      Real.cos θ + (1 / 3) * (Real.sqrt 3 * Real.sin θ) := by
  have hroot : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hroot0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [Real.sin_pi_sub, Real.sin_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
  field_simp
  linear_combination -Real.sin θ * hroot

theorem Triangle.sixty_rational_side_ratios (P : Triangle)
    (hangle : P.angleC = Real.pi / 3) (q : ℚ)
    (hq : (q : ℝ) = Real.sqrt 3 * Real.tan (P.angleA / 2)) :
    ∃ a b : ℚ, 0 < a ∧ 0 < b ∧
      dist P.b P.c = dist P.a P.b * a ∧
      dist P.a P.c = dist P.a P.b * b := by
  obtain ⟨hcos, hsin⟩ := scaled_half_tangent_formulas P.angleA (q : ℝ)
    P.angleA_pos P.angleA_lt_pi hq
  let a : ℚ := 4 * q / (3 + q ^ 2)
  let b : ℚ := (3 - q ^ 2 + 2 * q) / (3 + q ^ 2)
  have hA : Real.sin P.angleA / Real.sin P.angleC = (a : ℝ) := by
    rw [hangle, sin_over_sin_sixty, hsin]
    dsimp [a]
    push_cast
    ring
  have hBangle : P.angleB = Real.pi - (P.angleA + Real.pi / 3) := by
    linarith [P.angle_sum]
  have hB : Real.sin P.angleB / Real.sin P.angleC = (b : ℝ) := by
    rw [hangle, hBangle, sin_sixty_complement_ratio, hcos, hsin]
    dsimp [b]
    push_cast
    ring
  have hAB : 0 < dist P.a P.b := dist_pos.mpr P.a_ne_b
  have haSide : dist P.b P.c = dist P.a P.b * a := by
    rw [P.sideA_over_C, mul_div_assoc, hA]
  have hbSide : dist P.a P.c = dist P.a P.b * b := by
    rw [P.sideB_over_C, mul_div_assoc, hB]
  have ha : (0 : ℝ) < a := by
    have h : 0 < dist P.b P.c := dist_pos.mpr P.b_ne_c
    rw [haSide] at h
    exact pos_of_mul_pos_right h hAB.le
  have hb : (0 : ℝ) < b := by
    have h : 0 < dist P.a P.c := dist_pos.mpr P.swapBC.a_ne_b
    rw [hbSide] at h
    exact pos_of_mul_pos_right h hAB.le
  exact ⟨a, b, by exact_mod_cast ha, by exact_mod_cast hb, haSide, hbSide⟩

/-- The full fourth-family sufficient condition, expressed using the actual
Euclidean angles of an arbitrary nondegenerate triangle. -/
theorem Triangle.admitsNonsquareTiling_of_sixty_rational_half_tangent (P : Triangle)
    (hangle : P.angleC = Real.pi / 3)
    (hrat : ∃ q : ℚ, (q : ℝ) = Real.sqrt 3 * Real.tan (P.angleA / 2)) :
    AdmitsNonsquareTiling P := by
  obtain ⟨q, hq⟩ := hrat
  obtain ⟨a, b, ha, hb, hA, hB⟩ := P.sixty_rational_side_ratios hangle q hq
  have hT := P.rotate.rotate.admitsNonsquareTiling_of_sixty_rational_sides
    (by simpa only [Triangle.angleA_rotate, Triangle.angleB_rotate] using hangle)
    b a 1 hb ha (by norm_num) (dist P.a P.b) (dist_pos.mpr P.a_ne_b)
    (by simpa only [Triangle.rotate, dist_comm] using hB)
    (by simpa only [Triangle.rotate, dist_comm] using hA)
    (by simp [Triangle.rotate])
  exact admitsNonsquareTiling_of_carrier_eq hT
    (P.rotate.rotate_carrier.trans P.rotate_carrier)

end Erdos633
