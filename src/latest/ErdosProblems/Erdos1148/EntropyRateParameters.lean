import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Parameters for a finite-partition entropy rate arbitrarily close to one -/

namespace Erdos1148.DukeArithmetic

theorem exists_entropy_rate_parameters {ε L : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) (hL : 0 ≤ L) :
    ∃ σ κ m₀ δ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧ 0 < κ ∧ 0 < m₀ ∧ 0 < δ ∧
      m₀ = 1 - (1 + κ⁻¹) * δ ∧ 0 ≤ 1 - 2 * σ - κ * L ∧
      1 - ε < m₀ * (1 - 2 * σ - κ * L) := by
  let σ := ε / 8
  let κ := ε / (8 * (L + 1))
  let m₀ := 1 - ε / 8
  let δ := (ε / 8) / (1 + κ⁻¹)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσhalf : σ ≤ 1 / 2 := by dsimp [σ]; linarith
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hm₀ : 0 < m₀ := by dsimp [m₀]; linarith
  have hden : 0 < 1 + κ⁻¹ := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : (1 + κ⁻¹) * δ = ε / 8 := by
    dsimp only [δ]
    exact mul_div_cancel₀ _ hden.ne'
  have hκeq : κ * (8 * (L + 1)) = ε := by
    dsimp only [κ]
    exact div_mul_cancel₀ _ (by positivity : 8 * (L + 1) ≠ 0)
  have hκL : κ * L ≤ ε / 8 := by nlinarith [hκ.le]
  have hq : 1 - 3 * ε / 8 ≤ 1 - 2 * σ - κ * L := by dsimp only [σ]; linarith
  have hqpos : 0 ≤ 1 - 2 * σ - κ * L := by linarith
  have hprod := mul_le_mul_of_nonneg_left hq hm₀.le
  refine ⟨σ, κ, m₀, δ, hσ, hσhalf, hκ, hm₀, hδ, ?_, hqpos, ?_⟩
  · dsimp only [m₀]
    rw [hδeq]
  · dsimp only [m₀] at hprod ⊢
    nlinarith [sq_nonneg ε]

end Erdos1148.DukeArithmetic
