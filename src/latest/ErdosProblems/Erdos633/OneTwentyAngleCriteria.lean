import ErdosProblems.Erdos633.OneTwentyTrigonometry
import ErdosProblems.Erdos633.OneTwentyRationalCriteria

/-!
# The fifth and eighth sufficient angle conditions

These theorems start with the Euclidean angles of an arbitrary triangle.
Rational half-angle tangent data produce the actual side ratios, and the
unconditional Y and U₂ constructions then supply nonsquare congruent tilings.
-/

namespace Erdos633

theorem Triangle.admitsNonsquareTiling_of_double_angle_half_tangent (P : Triangle)
    (hdouble : P.angleB = 2 * P.angleA)
    (hrat : ∃ q : ℚ, (q : ℝ) = Real.sqrt 3 * Real.tan (P.angleA / 2)) :
    AdmitsNonsquareTiling P := by
  obtain ⟨q, hq⟩ := hrat
  have hα1 : P.angleA < Real.pi / 3 := by linarith [P.angle_sum, P.angleC_pos]
  have hC : P.angleC = Real.pi - 3 * P.angleA := by linarith [P.angle_sum]
  obtain ⟨a, b, ha, hb, hc, hsA, _, hcosA, _⟩ :=
    oneTwenty_rational_trigonometric_parameters P.angleA P.angleA_pos hα1 q hq
  have hcR : (a : ℝ) ^ 2 + (a : ℝ) * b + (b : ℝ) ^ 2 = 1 := by exact_mod_cast hc
  have hsin0 := ne_of_gt P.sin_angleA_pos
  have hBside : dist P.a P.c = dist P.b P.c * ((a : ℝ) + 2 * b) := by
    rw [P.sideB_over_A, hdouble, Real.sin_two_mul, hcosA]
    field_simp
  have hCside : dist P.a P.b = dist P.b P.c * (3 * (b : ℝ) * (a + b)) := by
    rw [P.sideC_over_A, hC, Real.sin_pi_sub,
      oneTwenty_sin_three P.angleA (a : ℝ) b hsA hcR]
    field_simp
  have hT := P.swapBC.admitsNonsquareTiling_of_U_two_rational_sides a b ha hb hc
    (dist P.b P.c) (dist_pos.mpr P.b_ne_c)
    (by simpa only [Triangle.swapBC] using hBside)
    (by simpa only [Triangle.swapBC] using hCside)
    (by simp only [Triangle.swapBC, dist_comm])
  exact admitsNonsquareTiling_of_carrier_eq hT P.swapBC_carrier

theorem Triangle.admitsNonsquareTiling_of_Y_angle_relation (P : Triangle)
    (hrelation : P.angleC = 2 * P.angleA + P.angleB / 2)
    (hrat : ∃ q : ℚ, (q : ℝ) = Real.sqrt 3 * Real.tan (P.angleA / 2)) :
    AdmitsNonsquareTiling P := by
  obtain ⟨q, hq⟩ := hrat
  have hα1 : P.angleA < Real.pi / 3 := by linarith [P.angle_sum, P.angleB_pos]
  have hB : P.angleB = 2 * (Real.pi / 3 - P.angleA) := by linarith [P.angle_sum]
  have hC : P.angleC = Real.pi / 3 + P.angleA := by linarith [P.angle_sum]
  obtain ⟨a, b, ha, hb, hc, hsA, hsB, hcosA, hcosB⟩ :=
    oneTwenty_rational_trigonometric_parameters P.angleA P.angleA_pos hα1 q hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have ha0 := ne_of_gt haR
  have ht : Real.sin (Real.pi / 3) ≠ 0 := by
    rw [Real.sin_pi_div_three]
    positivity
  apply P.admitsNonsquareTiling_of_Y_rational_sides a b ha hb hc
    (dist P.b P.c / (a : ℝ)) (div_pos (dist_pos.mpr P.b_ne_c) haR)
  · rw [P.sideC_over_A, hC, oneTwenty_sin_sixty_add P.angleA (a : ℝ) b hsA hcosA, hsA]
    field_simp
  · rw [P.sideB_over_A, hB, Real.sin_two_mul, hsB, hcosB, hsA]
    field_simp
  · field_simp

end Erdos633
