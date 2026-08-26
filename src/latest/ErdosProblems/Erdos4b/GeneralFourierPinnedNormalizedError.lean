/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedTauDecay
import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularLowerBound
import ErdosProblems.Erdos4b.SourcePrimeIntervalLowerBound

/-!
# Scalar estimates for normalizing the pinned prime-count error

The positive singular-series and interval-prime-count lower bounds
are retained in the denominator. A sufficiently strong inverse-log
saving leaves an explicit bound proportional to `1/V`.
-/

namespace Erdos4b

noncomputable section

theorem pinnedScaleProduct_le_ambient_power
    (K : ℕ) {V LE : ℝ} (hV : 1 ≤ V) (hLE : 0 ≤ LE) (hLEV : LE ≤ V) :
    V ^ (K - 1) * LE ^ (K - 1) ≤ V ^ (2 * K) := by
  have hD : V ^ (K - 1) ≤ V ^ K := pow_le_pow_right₀ hV (Nat.sub_le K 1)
  have hE : LE ^ (K - 1) ≤ V ^ K := (pow_le_pow_left₀ hLE hLEV _).trans hD
  calc
    _ ≤ V ^ K * V ^ K := mul_le_mul hD hE (pow_nonneg hLE _) (by positivity)
    _ = _ := by rw [← pow_two, ← pow_mul, Nat.mul_comm K 2]

theorem normalized_pinned_error_le_inverse_ambient
    (D J : ℕ) {δ C X V scale series count err : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hX : 0 < X) (hV : 0 < V)
    (hscale : scale ≤ V ^ D)
    (hseries : (1 : ℝ) / 2 ≤ series)
    (hcount : δ * X / (2 * V ^ (J + 1)) ≤ count)
    (herr0 : 0 ≤ err)
    (herr : err ≤ 2 * C * 2 ^ (D + J + 2) * X / V ^ (D + J + 2)) :
    scale / (series * count) * err ≤ 8 * C * 2 ^ (D + J + 2) / (δ * V) := by
  have hcount0 : 0 < count := (by positivity : 0 < δ * X / (2 * V ^ (J + 1))).trans_le hcount
  have hseries0 : 0 < series := lt_of_lt_of_le (by norm_num) hseries
  have hden : (1 / 2 : ℝ) * (δ * X / (2 * V ^ (J + 1))) ≤ series * count :=
    mul_le_mul hseries hcount (by positivity) hseries0.le
  calc
    _ = (scale * err) / (series * count) := by ring
    _ ≤ (V ^ D * (2 * C * 2 ^ (D + J + 2) * X / V ^ (D + J + 2))) /
        ((1 / 2 : ℝ) * (δ * X / (2 * V ^ (J + 1)))) := by
      apply div_le_div₀ (by positivity) _ (by positivity) hden
      exact mul_le_mul hscale herr herr0 (by positivity)
    _ = _ := by
      have hp : V ^ (D + J + 2) = V ^ D * V ^ (J + 1) * V := by
        simp only [pow_add, pow_succ]
        ring
      rw [hp]
      field_simp
      ring

end

end Erdos4b
