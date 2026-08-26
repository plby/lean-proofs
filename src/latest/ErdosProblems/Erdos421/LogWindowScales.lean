import ErdosProblems.Erdos421.WindowVarianceParameters

/-! # Logarithmic reference scales and absorption of the variance error terms -/

namespace Erdos421

open Filter Topology

theorem logarithmic_window_low_power {L ℓ A ρ : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hρupper : ρ ≤ L ^ (-(3 * ℓ + A + 1) / 2)) :
    ρ ^ 2 * (L ^ ℓ) ^ 3 ≤ L ^ (-A - 1) := by
  calc
    _ ≤ (L ^ (-(3 * ℓ + A + 1) / 2)) ^ 2 * (L ^ ℓ) ^ 3 := by gcongr
    _ = L ^ ((-(3 * ℓ + A + 1) / 2) * 2 + ℓ * 3) := by
      rw [← Real.rpow_mul_natCast hL.le, ← Real.rpow_mul_natCast hL.le, ← Real.rpow_add hL]
      norm_num
    _ = _ := by congr 1; ring

theorem constant_inverse_log_saving (C A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, C * (Real.log X) ^ (-A - 1) ≤ ε / (Real.log X) ^ A := by
  have ht : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (C / ε)),
    eventually_ge_atTop (2 : ℕ)] with X hlarge hX
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hLA : 0 < (Real.log X) ^ A := Real.rpow_pos_of_pos hL _
  have hc : C ≤ ε * Real.log X := by
    have h := (div_le_iff₀ hε).mp hlarge
    linarith
  have he : (Real.log X) ^ (-A - 1) = 1 / ((Real.log X) ^ A * Real.log X) := by
    rw [show -A - 1 = -(A + 1) by ring, Real.rpow_neg hL.le,
      Real.rpow_add hL, Real.rpow_one, one_div]
  rw [he, mul_one_div]
  apply (div_le_div_iff₀ (mul_pos hLA hL) hLA).mpr
  nlinarith

theorem short_window_below_log_scale {d : ℝ} (hd : 0 < d) (B : ℝ) :
    ∀ᶠ X : ℕ in atTop, 4 * Real.pi / (X : ℝ) ^ d ≤ (Real.log X) ^ (-B) := by
  have hp : 0 < 4 * Real.pi := by positivity
  filter_upwards [inverse_log_above_inverse_power hd (inv_pos.mpr hp) B,
    eventually_ge_atTop (2 : ℕ)] with X hsave hX
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
  have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hm := mul_le_mul_of_nonneg_left hsave hp.le
  rw [Real.rpow_neg hXp.le] at hm
  rw [Real.rpow_neg hL.le]
  simpa only [div_eq_mul_inv, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] using hm

end Erdos421
