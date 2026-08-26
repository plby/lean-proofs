import ErdosProblems.Erdos421.RoughWindowComparison

/-! # Retaining the actual interval length in the rough-window estimate -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem additiveRoughWindow_length_mean (A : ℝ) {ε τ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) :
    ∀ᶠ X : ℕ in atTop, ∀ D z : ℕ, 0 < D → 2 ≤ z →
      ((z * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
      ∀ (Y u v : ℝ) (B : ℕ), (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y →
      0 ≤ u → u ≤ v → v - u ≤ X → v + Y ≤ B →
      (∫ x in u..v, |additiveRoughWindow B z Y x - roughEulerProduct z| ^ 2) ≤
        3 * (v - u) * (ε * roughEulerProduct z) ^ 2 + τ * X / (Real.log X) ^ A := by
  have hτ6 : 0 < τ / 6 := by positivity
  filter_upwards [eventually_ge_atTop 1, canonicalUpper_window_mean A hτ6,
    canonicalLower_window_mean A hτ6] with X hX hU hL
  intro D z hD hz hMX hlevel Y u v B hY hu huv hlen hB
  have hYpos : 0 < Y := (Real.rpow_pos_of_pos (by exact_mod_cast hX) _).trans_le hY
  have hDX : ((D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) := by
    apply le_trans _ hMX
    exact_mod_cast Nat.le_mul_of_pos_left (D ^ 2) (by omega : 0 < z)
  have hbU := hU D z hD hDX Y u v hY huv hlen
  have hbL := hL D z hD (by omega) hMX Y u v hY huv hlen
  have hb := additiveRoughWindow_mean_square_errors hD hz hε hε1 hlevel hYpos hu huv hB
  change (∫ x in u..v, ‖sieveWindowError (D ^ 2) (canonicalUpperSieve D z) Y x‖ ^ 2) ≤ _ at hbU
  change (∫ x in u..v,
    ‖sieveWindowError (z * D ^ 2) (lowerSieveCoefficient D z) Y x‖ ^ 2) ≤ _ at hbL
  apply hb.trans
  calc
    _ ≤ 3 * (v - u) * (ε * roughEulerProduct z) ^ 2 +
        3 * (τ / 6 * X / (Real.log X) ^ A) + 3 * (τ / 6 * X / (Real.log X) ^ A) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbU (by norm_num)))
        (mul_le_mul_of_nonneg_left hbL (by norm_num))
    _ = _ := by ring

theorem additiveRoughWindow_length_comparison (A : ℝ) {ε τ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) :
    ∀ᶠ X : ℕ in atTop, ∀ D z : ℕ, 0 < D → 2 ≤ z →
      ((z * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
      ∀ (Y₁ Y₂ u v : ℝ) (B : ℕ), (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y₁ →
      (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y₂ →
      0 ≤ u → u ≤ v → v - u ≤ X → v + Y₁ ≤ B → v + Y₂ ≤ B →
      (∫ x in u..v, |additiveRoughWindow B z Y₁ x - additiveRoughWindow B z Y₂ x| ^ 2) ≤
        12 * (v - u) * (ε * roughEulerProduct z) ^ 2 + τ * X / (Real.log X) ^ A := by
  filter_upwards [additiveRoughWindow_length_mean A hε hε1 (by positivity : 0 < τ / 4)] with X hX
  intro D z hD hz hMX hlevel Y₁ Y₂ u v B hY₁ hY₂ hu huv hlen hB₁ hB₂
  have h₁ := hX D z hD hz hMX hlevel Y₁ u v B hY₁ hu huv hlen hB₁
  have h₂ := hX D z hD hz hMX hlevel Y₂ u v B hY₂ hu huv hlen hB₂
  have hb := continuous_interval_square_difference_le (additiveRoughWindow B z Y₁)
    (additiveRoughWindow B z Y₂) (additiveRoughWindow_continuous B z Y₁)
    (additiveRoughWindow_continuous B z Y₂) (roughEulerProduct z) huv
  apply hb.trans
  calc
    _ ≤ 2 * (3 * (v - u) * (ε * roughEulerProduct z) ^ 2 + τ / 4 * X / (Real.log X) ^ A) +
        2 * (3 * (v - u) * (ε * roughEulerProduct z) ^ 2 + τ / 4 * X / (Real.log X) ^ A) :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ (by norm_num))
        (mul_le_mul_of_nonneg_left h₂ (by norm_num))
    _ = _ := by ring

end Erdos421
