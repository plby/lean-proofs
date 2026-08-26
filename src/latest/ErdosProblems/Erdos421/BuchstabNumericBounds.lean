import ErdosProblems.Erdos421.BuchstabInitialValues

/-! # Rigorous upper and lower bounds for the finite Buchstab function -/

namespace Erdos421

open MeasureTheory

theorem finiteBuchstab_scaled_increment_le (n : ℕ) {a b C : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hC : ∀ t ∈ Set.Icc (a - 1) (b - 1), finiteBuchstab n t ≤ C) :
    b * finiteBuchstab (n + 1) b - a * finiteBuchstab (n + 1) a ≤ (b - a) * C := by
  rw [finiteBuchstab_scaled_increment n ha hab]
  have hc : Continuous (fun t : ℝ ↦ finiteBuchstab n (t - 1)) :=
    (finiteBuchstab_continuous n).comp (continuous_id.sub continuous_const)
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    (hc.intervalIntegrable a b) (intervalIntegrable_const (c := C)) (by
      intro t ht
      exact hC (t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm

theorem finiteBuchstab_scaled_increment_ge (n : ℕ) {a b C : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hC : ∀ t ∈ Set.Icc (a - 1) (b - 1), C ≤ finiteBuchstab n t) :
    (b - a) * C ≤ b * finiteBuchstab (n + 1) b - a * finiteBuchstab (n + 1) a := by
  rw [finiteBuchstab_scaled_increment n ha hab]
  have hc : Continuous (fun t : ℝ ↦ finiteBuchstab n (t - 1)) :=
    (finiteBuchstab_continuous n).comp (continuous_id.sub continuous_const)
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    (intervalIntegrable_const (c := C)) (hc.intervalIntegrable a b) (by
      intro t ht
      exact hC (t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm

theorem finiteBuchstab_upper (n : ℕ) {u : ℝ} (hu : 2 ≤ u) :
    finiteBuchstab n u ≤ 23 / 40 := by
  induction n generalizing u with
  | zero =>
    rw [finiteBuchstab, max_eq_right (show 1 ≤ u by linarith)]
    apply (div_le_iff₀ (show 0 < u by linarith)).mpr
    linarith
  | succ n ih =>
    by_cases hu3 : u ≤ 3
    · exact finiteBuchstab_initial_upper n ⟨hu, hu3⟩
    have h3u : 3 ≤ u := by linarith
    have hi := finiteBuchstab_scaled_increment_le n (by norm_num : (2 : ℝ) ≤ 3) h3u
      (C := 23 / 40) (fun t ht ↦ ih (by linarith [ht.1]))
    have h3 := finiteBuchstab_initial_upper n (u := 3) ⟨by norm_num, le_rfl⟩
    apply (mul_le_mul_iff_right₀ (show 0 < u by linarith)).mp
    nlinarith

theorem finiteBuchstab_lower_middle (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (3 : ℝ) (7 / 2)) :
    (11 / 20 : ℝ) ≤ finiteBuchstab (n + 2) u := by
  have hi := finiteBuchstab_scaled_increment_ge (n + 1)
    (by norm_num : (2 : ℝ) ≤ 3) hu.1 (C := 1 / 2) (by
      intro t ht
      apply finiteBuchstab_initial_lower_half n
      exact ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩)
  have h3 := finiteBuchstab_at_three (n + 1)
  apply (mul_le_mul_iff_right₀ (show 0 < u by linarith [hu.1])).mp
  nlinarith [hu.2]

theorem finiteBuchstab_lower (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (5 / 2 : ℝ) (n + 3)) :
    (11 / 20 : ℝ) ≤ finiteBuchstab (n + 1) u := by
  induction n generalizing u with
  | zero =>
    exact finiteBuchstab_initial_lower 0 (by simpa using hu)
  | succ n ih =>
    by_cases hu3 : u ≤ 3
    · exact finiteBuchstab_initial_lower (n + 1) ⟨hu.1, hu3⟩
    by_cases hu7 : u ≤ 7 / 2
    · exact finiteBuchstab_lower_middle n ⟨by linarith, hu7⟩
    have huupper : u ≤ (n : ℝ) + 4 := by
      have hb := hu.2
      push_cast at hb
      linarith
    have hi := finiteBuchstab_scaled_increment_ge (n + 1)
      (by norm_num : (2 : ℝ) ≤ 7 / 2) (show 7 / 2 ≤ u by linarith) (C := 11 / 20) (by
        intro t ht
        apply ih
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hstart := finiteBuchstab_lower_middle n (u := 7 / 2) ⟨by norm_num, le_rfl⟩
    apply (mul_le_mul_iff_right₀ (show 0 < u by linarith [hu.1])).mp
    nlinarith

end Erdos421
