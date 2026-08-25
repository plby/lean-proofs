import ErdosProblems.Erdos1141.BurgessPowerScales

/-!
# Absorbing the three hyperbola error terms
-/

namespace Pollack17

open Filter

theorem eventually_three_power_errors_le {c a b d C D E : ℝ}
    (ha : a < c) (hb : b < c) (hd : d < c) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      C * (m : ℝ) ^ a + D * (m : ℝ) ^ b + E * (m : ℝ) ^ d ≤ (m : ℝ) ^ (c - τ) := by
  let τ : ℝ := min (c - a) (min (c - b) (c - d)) / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτa : a < c - τ := by
    have h := min_le_left (c - a) (min (c - b) (c - d))
    dsimp [τ] at hτ ⊢
    linarith
  have hτb : b < c - τ := by
    have h := (min_le_right (c - a) (min (c - b) (c - d))).trans (min_le_left _ _)
    dsimp [τ] at hτ ⊢
    linarith
  have hτd : d < c - τ := by
    have h := (min_le_right (c - a) (min (c - b) (c - d))).trans (min_le_right _ _)
    dsimp [τ] at hτ ⊢
    linarith
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [Burgess.eventually_const_mul_rpow_le (C := C) (d := 1 / 3) (by norm_num) hτa,
    Burgess.eventually_const_mul_rpow_le (C := D) (d := 1 / 3) (by norm_num) hτb,
    Burgess.eventually_const_mul_rpow_le (C := E) (d := 1 / 3) (by norm_num) hτd]
    with m hm₁ hm₂ hm₃
  linarith only [hm₁, hm₂, hm₃]

theorem eventually_divisor_error_le {c a σ : ℝ} (hc : 0 < c) (ha : a < c) (hσ : 0 < σ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ m : ℕ in atTop,
      2 * (m : ℝ) ^ a + (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) +
        4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) ≤ (m : ℝ) ^ (c - τ) := by
  let κ : ℝ := min σ 1 / 4
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκσ : κ < σ := by
    have h := min_le_left σ 1
    dsimp [κ] at hκ ⊢
    linarith
  have hκ1 : κ < 3 / 2 := by
    have h := min_le_right σ 1
    dsimp [κ]
    linarith
  obtain ⟨τ, hτ, h⟩ := eventually_three_power_errors_le
    (C := 2) (D := 7 + 2 * c) (E := 4) ha
    (show c - σ + κ < c by linarith) (show c - 3 / 2 + κ < c by linarith)
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [h, Burgess.eventually_one_add_log_le_rpow hκ, eventually_ge_atTop 1]
    with m hm hlog hm1
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
  have hfirst : (7 + 2 * c) * (m : ℝ) ^ (c - σ) * (1 + Real.log (m : ℝ)) ≤
      (7 + 2 * c) * (m : ℝ) ^ (c - σ + κ) := by
    rw [Real.rpow_add hm0, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsecond : 4 * (m : ℝ) ^ (c - 3 / 2) * (1 + Real.log (m : ℝ)) ≤
      4 * (m : ℝ) ^ (c - 3 / 2 + κ) := by
    rw [Real.rpow_add hm0, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  exact (add_le_add (add_le_add le_rfl hfirst) hsecond).trans hm

end Pollack17
