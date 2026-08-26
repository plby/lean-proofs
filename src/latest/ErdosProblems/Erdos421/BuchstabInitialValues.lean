import ErdosProblems.Erdos421.FiniteBuchstabFunction
import ErdosProblems.Erdos421.BuchstabLogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact initial values and scaled increments of the finite Buchstab function -/

namespace Erdos421

open MeasureTheory

theorem finiteBuchstab_initial_formula (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (2 : ℝ) 3) :
    finiteBuchstab (n + 1) u = (1 + Real.log (u - 1)) / u := by
  rw [finiteBuchstab_step n hu.1]
  have hi : (∫ t in (2 : ℝ)..u, finiteBuchstab n (t - 1)) =
      ∫ t in (2 : ℝ)..u, (t - 1)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hu.1] at ht
    change finiteBuchstab n (t - 1) = (t - 1)⁻¹
    rw [finiteBuchstab_initial n (u := t - 1)
      ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩, one_div]
  rw [hi, intervalIntegral.integral_comp_sub_right (fun t : ℝ ↦ t⁻¹) 1]
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num]
  rw [integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) (by linarith [hu.1]), div_one]

theorem finiteBuchstab_scaled_increment (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    b * finiteBuchstab (n + 1) b - a * finiteBuchstab (n + 1) a =
      ∫ t in a..b, finiteBuchstab n (t - 1) := by
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  have hscaled : ∀ u : ℝ, 2 ≤ u → u * finiteBuchstab (n + 1) u =
      1 + ∫ t in (2 : ℝ)..u, finiteBuchstab n (t - 1) := by
    intro u hu
    have hu0 : u ≠ 0 := by linarith
    rw [finiteBuchstab_step n hu]
    field_simp
  rw [hscaled b (ha.trans hab), hscaled a ha]
  have hc : Continuous (fun t : ℝ ↦ finiteBuchstab n (t - 1)) :=
    (finiteBuchstab_continuous n).comp (continuous_id.sub continuous_const)
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 2 a) (hc.intervalIntegrable a b)
  linarith only [hi]

theorem finiteBuchstab_initial_upper (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (2 : ℝ) 3) :
    finiteBuchstab (n + 1) u ≤ 23 / 40 := by
  rw [finiteBuchstab_initial_formula n hu]
  exact buchstab_initial_formula_upper hu.1

theorem finiteBuchstab_initial_lower_half (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (2 : ℝ) 3) :
    (1 / 2 : ℝ) ≤ finiteBuchstab (n + 1) u := by
  rw [finiteBuchstab_initial_formula n hu]
  exact buchstab_initial_formula_lower_half hu

theorem finiteBuchstab_initial_lower (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (5 / 2 : ℝ) 3) :
    (11 / 20 : ℝ) ≤ finiteBuchstab (n + 1) u := by
  rw [finiteBuchstab_initial_formula n ⟨by linarith [hu.1], hu.2⟩]
  exact buchstab_initial_formula_lower hu

theorem finiteBuchstab_at_three (n : ℕ) :
    (169 / 100 : ℝ) ≤ 3 * finiteBuchstab (n + 1) 3 := by
  rw [finiteBuchstab_initial_formula n ⟨by norm_num, le_rfl⟩]
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num]
  have h := log_two_ge_sixty_nine
  linarith

end Erdos421
