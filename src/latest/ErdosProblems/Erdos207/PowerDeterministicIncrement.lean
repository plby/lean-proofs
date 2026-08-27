/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerSelectorBounds

/-! # Combining the slope, Taylor error, and envelope increment on one power scale -/

namespace Erdos207

theorem deterministic_increment_power
    (N t df de slope e L C D : ℝ) (z b : ℕ)
    (hN : 0 < N) (ht : 6 ≤ t) (he : 0 ≤ e) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (henvelope : e ≤ N ^ (z + 1))
    (hCscale : C ≤ t) (hDscale : D ≤ t)
    (hclock : N ^ 2 / t ^ (2 * b) ≤ L)
    (hslope : |slope| ≤ N ^ z / N * t ^ (5 * b + 6))
    (hTaylor : |df - slope| ≤ C * e / L) (hGrowth : |de| ≤ D * e / L) :
    |df| + |de| ≤ N ^ z / N * t ^ (5 * b + 7) := by
  have htpos : 0 < t := by linarith
  have hCbound := coefficient_envelope_div_clock_power N t e C L z b hN htpos he hC
    henvelope hCscale hclock
  have hDbound := coefficient_envelope_div_clock_power N t e D L z b hN htpos he hD
    henvelope hDscale hclock
  have hpower : t ^ (2 * b + 1) ≤ t ^ (5 * b + 6) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hscaled := mul_le_mul_of_nonneg_left hpower (show 0 ≤ N ^ z / N by positivity)
  have hdf : |df| ≤ |df - slope| + |slope| := by
    calc
      |df| = |(df - slope) + slope| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hTaylor' := (hTaylor.trans hCbound).trans hscaled
  have hGrowth' := (hGrowth.trans hDbound).trans hscaled
  calc
    _ ≤ (N ^ z / N) * (3 * t ^ (5 * b + 6)) := by linarith only [hdf, hslope, hTaylor', hGrowth']
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (real_coeff_mul_pow_le_pow (by linarith) (by linarith : (3 : ℝ) ≤ t) (by omega)) (by positivity)

end Erdos207
