import ErdosProblems.Erdos421.LogarithmicMeasureMean
import ErdosProblems.Erdos421.LogarithmicGridError

/-! # The unconditional logarithmic rough-window variance estimate -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem logarithmicRoughWindow_variance {ε τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) :
    ∀ᶠ X : ℕ in atTop, ∀ D z : ℕ, 0 < D → 2 ≤ z →
      ((z * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
      ∀ (B : ℕ) (δ₁ δ₂ : ℝ), 3 * X ≤ B → 0 < δ₁ → 0 < δ₂ →
        δ₁ ≤ (Real.log X) ^ (-2 : ℝ) → δ₂ ≤ (Real.log X) ^ (-2 : ℝ) →
        (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₁ * X → (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₂ * X →
        (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
          |logarithmicRoughWindow B z δ₁ y - logarithmicRoughWindow B z δ₂ y| ^ 2) ≤
            36 * (ε * roughEulerProduct z) ^ 2 + τ / (Real.log X) ^ 2 := by
  obtain ⟨K, hK, hmean⟩ := exists_logarithmic_variance_with_grid
  let C := 2 + 54 * K ^ 2
  have hClog : ∀ᶠ X : ℕ in atTop, max 2 (C / τ) ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  have hlogpower : ∀ᶠ X : ℕ in atTop, (Real.log X) ^ (2 : ℕ) ≤ (X : ℝ) := by
    have h := eventually_power_log_saving (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) 0 2
    simpa only [sub_self, Real.rpow_zero, one_mul, Real.rpow_two, div_one] using h
  filter_upwards [eventually_ge_atTop 1, hClog, hlogpower,
    hmean 6 ε 1 hε hε1 (by norm_num)] with X hX hCL hpower hmeanX
  intro D z hD hz hMX hlevel B δ₁ δ₂ hB hδ₁ hδ₂ hδ₁L hδ₂L hY₁ hY₂
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hL2 : 2 ≤ Real.log X := (le_max_left _ _).trans hCL
  have hLp : 0 < Real.log X := by linarith
  have hLs : 0 < (Real.log X) ^ (2 : ℕ) := sq_pos_of_pos hLp
  let N := ⌈(Real.log X) ^ (2 : ℕ)⌉₊
  let ρ := ((Real.log X) ^ (2 : ℕ))⁻¹
  have hN : 0 < N := Nat.one_le_ceil_iff.mpr hLs
  have hρpos : 0 < ρ := inv_pos.mpr hLs
  have hρhalf : ρ ≤ 1 / 2 := by
    dsimp only [ρ]
    rw [inv_eq_one_div, div_le_iff₀ hLs]
    nlinarith
  have hrpow : (Real.log X) ^ (-2 : ℝ) = ρ := by
    rw [Real.rpow_neg hLp.le]
    norm_num [ρ]
  rw [hrpow] at hδ₁L hδ₂L
  have hm := hmeanX D z hD hz hMX hlevel N B δ₁ δ₂ ρ hN hB hδ₁ hδ₂ hδ₁L hδ₂L hρhalf hY₁ hY₂
  norm_num only [mul_one, Real.rpow_ofNat] at hm
  have he := logarithmic_grid_error_le hK.le (by linarith : 1 ≤ Real.log X) hpower hρpos.le le_rfl
  change (N : ℝ) / (Real.log X) ^ (6 : ℕ) +
    6 * (K * (ρ + (X : ℝ)⁻¹ + (N : ℝ)⁻¹)) ^ 2 ≤ C / (Real.log X) ^ (4 : ℕ) at he
  have hCbound : C ≤ τ * (Real.log X) ^ (2 : ℕ) := by
    have hc := (div_le_iff₀ hτ).mp ((le_max_right 2 (C / τ)).trans hCL)
    have hs : Real.log X ≤ (Real.log X) ^ (2 : ℕ) := by nlinarith
    have ht := mul_le_mul_of_nonneg_left hs hτ.le
    nlinarith
  have hsmall : C / (Real.log X) ^ (4 : ℕ) ≤ τ / (Real.log X) ^ (2 : ℕ) := by
    calc
      _ ≤ (τ * (Real.log X) ^ (2 : ℕ)) / (Real.log X) ^ (4 : ℕ) :=
        div_le_div_of_nonneg_right hCbound (by positivity)
      _ = _ := by field_simp
  linarith

end Erdos421
