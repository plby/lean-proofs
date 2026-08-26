import ErdosProblems.Erdos633.GroupOneTrigonometry
import ErdosProblems.Erdos633.UTiling

/-!
# The group-one sufficient conditions in Euclidean angle language

The sine rule identifies arbitrary triangles satisfying the two angle
relations with the already constructed U and V similarity classes.
In the V case, the parameter is `2 sin(A/4)`, including its factor of two.
-/

namespace Erdos633

theorem Triangle.admitsNonsquareTiling_of_U_angles (P : Triangle)
    (hdouble : P.angleB = 2 * P.angleA) (s : ℚ)
    (hs : (s : ℝ) = 2 * Real.sin (P.angleA / 2)) : AdmitsNonsquareTiling P := by
  have hα1 : P.angleA < Real.pi / 3 := by
    linarith [P.angle_sum, P.angleC_pos]
  have hC : P.angleC = Real.pi - 3 * P.angleA := by linarith [P.angle_sum]
  obtain ⟨hsR0, hsR1⟩ := groupOne_parameter_range P.angleA (s : ℝ) P.angleA_pos hα1 hs
  have hs0 : 0 < s := by exact_mod_cast hsR0
  have hs1 : s < 1 := by exact_mod_cast hsR1
  let q := dist P.b P.c
  have hq : 0 < q := dist_pos.mpr P.b_ne_c
  have hsin := ne_of_gt P.sin_angleA_pos
  have hsideB : dist P.a P.c = q * (2 - (s : ℝ) ^ 2) := by
    dsimp [q]
    rw [P.sideB_over_A, hdouble, groupOne_sin_two P.angleA (s : ℝ) hs]
    field_simp
  have hsideC : dist P.a P.b = q * ((1 - (s : ℝ) ^ 2) * (3 - (s : ℝ) ^ 2)) := by
    dsimp [q]
    rw [P.sideC_over_A, hC, Real.sin_pi_sub, groupOne_sin_three P.angleA (s : ℝ) hs]
    field_simp
  have hrot : AdmitsNonsquareTiling P.rotate := by
    apply P.rotate.admitsNonsquareTiling_of_U_sides s hs0 hs1 q hq
    · change Complex.normSq (P.c - P.b) = q ^ 2
      exact normSq_sub_eq_dist_sq _ _
    · change Complex.normSq (P.a - P.b) =
        q ^ 2 * ((1 - (s : ℝ) ^ 2) * (3 - (s : ℝ) ^ 2)) ^ 2
      rw [normSq_sub_eq_dist_sq, dist_comm P.b P.a, hsideC]
      ring
    · change Complex.normSq (P.a - P.c) = q ^ 2 * (2 - (s : ℝ) ^ 2) ^ 2
      rw [normSq_sub_eq_dist_sq, dist_comm P.c P.a, hsideB]
      ring
  exact admitsNonsquareTiling_of_carrier_eq hrot P.rotate_carrier

/-- The published double-angle sufficient condition with rational half-angle sine. -/
theorem Triangle.admitsNonsquareTiling_of_double_angle_half_sine (P : Triangle)
    (hdouble : P.angleB = 2 * P.angleA)
    (hrat : ∃ s : ℚ, (s : ℝ) = Real.sin (P.angleA / 2)) : AdmitsNonsquareTiling P := by
  obtain ⟨s, hs⟩ := hrat
  apply P.admitsNonsquareTiling_of_U_angles hdouble (2 * s)
  push_cast
  rw [hs]

theorem Triangle.V_parameter_range (P : Triangle)
    (hC : P.angleC = P.angleA / 2 + P.angleB) :
    0 < 2 * Real.sin (P.angleA / 4) ∧ 2 * Real.sin (P.angleA / 4) < 1 := by
  have hrel : 3 * (P.angleA / 2) + 2 * P.angleB = Real.pi := by linarith [P.angle_sum]
  have hα0 : 0 < P.angleA / 2 := by linarith [P.angleA_pos]
  have hα1 : P.angleA / 2 < Real.pi / 3 := by linarith [P.angleB_pos]
  apply groupOne_parameter_range (P.angleA / 2) _ hα0 hα1
  congr 2
  ring

/-- The V sufficient condition, with the exact nonsquare parameter restriction. -/
theorem Triangle.admitsNonsquareTiling_of_V_angles (P : Triangle)
    (hC : P.angleC = P.angleA / 2 + P.angleB) (s : ℚ)
    (hs : (s : ℝ) = 2 * Real.sin (P.angleA / 4))
    (hns : ¬ IsSquare (2 - s ^ 2)) : AdmitsNonsquareTiling P := by
  let α := P.angleA / 2
  have hrel : 3 * α + 2 * P.angleB = Real.pi := by dsimp [α]; linarith [P.angle_sum]
  have hs' : (s : ℝ) = 2 * Real.sin (α / 2) := by
    rw [show α / 2 = P.angleA / 4 by dsimp [α]; ring]
    exact hs
  have hparam := P.V_parameter_range hC
  rw [← hs] at hparam
  have hs0 : 0 < s := by exact_mod_cast hparam.1
  have hs1 : s < 1 := by exact_mod_cast hparam.2
  have hsinC : Real.sin P.angleC = Real.cos (α / 2) := by
    rw [hC]
    exact groupOne_sin_sum α P.angleB hrel
  have hsinB := groupOne_sin_beta α P.angleB (s : ℝ) hrel hs'
  have hsinA : Real.sin P.angleA = Real.cos (α / 2) * ((s : ℝ) * (2 - (s : ℝ) ^ 2)) := by
    rw [show P.angleA = 2 * α by dsimp [α]; ring]
    exact groupOne_sin_two_half α (s : ℝ) hs'
  have hcos : Real.cos (α / 2) ≠ 0 := by
    rw [← hsinC]
    exact ne_of_gt P.sin_angleC_pos
  let q := dist P.a P.b
  have hq : 0 < q := dist_pos.mpr P.a_ne_b
  have hsideB : dist P.a P.c = q * (1 - (s : ℝ) ^ 2) := by
    dsimp [q]
    rw [P.sideB_over_C, hsinB, hsinC]
    field_simp
  have hsideA : dist P.b P.c = q * ((s : ℝ) * (2 - (s : ℝ) ^ 2)) := by
    dsimp [q]
    rw [P.sideA_over_C, hsinA, hsinC]
    field_simp
  apply P.admitsNonsquareTiling_of_V_sides s hs0 hs1 hns q hq
  · exact normSq_sub_eq_dist_sq _ _
  · rw [normSq_sub_eq_dist_sq, hsideB]
    ring
  · rw [normSq_sub_eq_dist_sq, hsideA]
    ring

/-- Equivalent integer formulation: `2 sin(A/4) = u/d` and `2d²-u²`
is nonsquare. No reduction or coprimality assumption is needed. -/
theorem Triangle.admitsNonsquareTiling_of_V_integer_parameter (P : Triangle)
    (hC : P.angleC = P.angleA / 2 + P.angleB) (u d : ℕ) (hd : 0 < d)
    (hs : 2 * Real.sin (P.angleA / 4) = (u : ℝ) / d)
    (hns : ¬ IsSquare (2 * d ^ 2 - u ^ 2)) : AdmitsNonsquareTiling P := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlt := (P.V_parameter_range hC).2
  rw [hs] at hlt
  have hud : u < d := by exact_mod_cast (div_lt_one hdR).mp hlt
  apply P.admitsNonsquareTiling_of_V_angles hC ((u : ℚ) / d)
  · push_cast
    exact hs.symm
  · intro h
    exact hns ((groupOne_V_isSquare_iff hud).mp h)

end Erdos633
