import ErdosProblems.Erdos421.WindowPlateauGeometry

/-! # A positive lower bound for the longer smoothed prime window -/

namespace Erdos421

open Complex
open scoped SchwartzMap

theorem prime_reference_window_lower_bound {B : ℝ} (hB : 0 ≤ B) :
    ∃ X₀ : ℝ, 1 < X₀ ∧ ∀ X : ℕ, X₀ ≤ X → ∀ (ρ y : ℝ) (hρ : 0 < ρ),
      2 / (Real.log X) ^ B ≤ ρ → Real.exp ρ ≤ 4 / 3 →
      (X : ℝ) ≤ Real.exp y → Real.exp y ≤ 3 * X / 2 →
      oneSidedWindowHeight / (8 * Real.log (2 * X)) ≤
        (schwartzDirichletWindow (primeBlockSupport X X) (fun _ ↦ 1) 1
          (normalizedSchwartzScale ρ hρ oneSidedSchwartzWindow) y).re := by
  obtain ⟨X₀, hX₀, hcount⟩ := prime_long_interval_card_lower_bound hB
  refine ⟨X₀, hX₀, ?_⟩
  intro X hX ρ y hρ hρlo hexp hlo hhi
  have hXp : (0 : ℝ) < X := by linarith
  have hlog : 0 < Real.log (2 * X) := Real.log_pos (by linarith)
  have hbounds := exponential_plateau_bounds hXp.le hρ.le hlo hhi hexp
  have horder := exponential_plateau_order hρ.le y
  have hlen : (X : ℝ) / (Real.log X) ^ B ≤
      Real.exp (y + 3 * ρ / 4) - Real.exp (y + ρ / 4) := by
    calc
      _ = (X : ℝ) * (2 / (Real.log X) ^ B) / 2 := by ring
      _ ≤ (X : ℝ) * ρ / 2 := by gcongr
      _ ≤ _ := hbounds.2.2
  have hcard := hcount X (Real.exp (y + ρ / 4)) (Real.exp (y + 3 * ρ / 4)) hX
    hbounds.1 horder hbounds.2.1 hlen
  have hupper : Real.exp (y + 3 * ρ / 4) ≤ (X + X : ℕ) := by
    simpa only [Nat.cast_add, two_mul] using hbounds.2.1
  have hwindow := prime_reference_window_plateau_bound X X hρ
    (by positivity : (0 : ℝ) < 2 * X) hbounds.1 hupper hbounds.2.1
  have hcardweight := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard oneSidedWindowHeight_pos.le)
    (by positivity : 0 ≤ ρ * (2 * X))
  calc
    _ = (((X : ℝ) * ρ / 2) / (2 * Real.log (2 * X))) * oneSidedWindowHeight /
        (ρ * (2 * X)) := by
      have hXn : (X : ℝ) ≠ 0 := hXp.ne'
      have hρn : ρ ≠ 0 := hρ.ne'
      field_simp
      ring
    _ ≤ ((Real.exp (y + 3 * ρ / 4) - Real.exp (y + ρ / 4)) / (2 * Real.log (2 * X))) *
        oneSidedWindowHeight / (ρ * (2 * X)) := by
      have hs := div_le_div_of_nonneg_right hbounds.2.2
        (by positivity : 0 ≤ 2 * Real.log (2 * X))
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs oneSidedWindowHeight_pos.le)
        (by positivity)
    _ ≤ _ := hcardweight.trans hwindow

end Erdos421
