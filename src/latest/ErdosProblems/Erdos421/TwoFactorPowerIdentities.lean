import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exact power identities for two-factor large-value interpolation -/

namespace Erdos421

theorem twoFactor_power_identity_a (u w R : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (u * w * R) ^ (2 * k) = (R * u) ^ (2 * k - 1) * (R * w ^ k) * u * w ^ k := by
  have he : 2 * k = (2 * k - 1) + 1 := by omega
  calc
    _ = (R * u) ^ (2 * k) * (w ^ k) ^ 2 := by
      rw [← pow_mul, show k * 2 = 2 * k by omega, ← mul_pow]
      congr 1
      ring
    _ = _ := by
      have hp : (R * u) ^ (2 * k) = (R * u) ^ (2 * k - 1) * (R * u) := by
        conv_lhs => rw [he, pow_succ]
      rw [hp]
      ring

theorem twoFactor_power_identity_b (u w R : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    (u * w * R) ^ (2 * k) =
      (R * u) ^ (2 * k - 3) * (R * u ^ 3) * (R * w ^ k) ^ 2 := by
  have he : 2 * k = (2 * k - 3) + 3 := by omega
  calc
    _ = (R * u) ^ (2 * k) * (w ^ k) ^ 2 := by
      rw [← pow_mul, show k * 2 = 2 * k by omega, ← mul_pow]
      congr 1
      ring
    _ = _ := by
      have hp : (R * u) ^ (2 * k) = (R * u) ^ (2 * k - 3) * (R * u) ^ 3 := by
        conv_lhs => rw [he, pow_add]
      rw [hp, mul_pow]
      ring

theorem twoFactor_power_identity_c (u w R : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (u * w * R) ^ (3 * k) = (R * u) ^ (3 * k - 1) * (R * w ^ (3 * k)) * u := by
  have he : 3 * k = (3 * k - 1) + 1 := by omega
  calc
    _ = (R * u) ^ (3 * k) * w ^ (3 * k) := by rw [← mul_pow]; congr 1; ring
    _ = _ := by
      have hp : (R * u) ^ (3 * k) = (R * u) ^ (3 * k - 1) * (R * u) := by
        conv_lhs => rw [he, pow_succ]
      rw [hp]
      ring

end Erdos421
