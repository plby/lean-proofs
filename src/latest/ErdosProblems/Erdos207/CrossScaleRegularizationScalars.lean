/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationInputPowerScalars
import ErdosProblems.Erdos207.KSSSDensityHorizon

/-! # Keep the global density scale in local sparse-process inequalities -/

namespace Erdos207

open scoped NNReal

theorem crossScale_density_ratio_lower
    (t u p tau n factor : ℝ≥0) (b c d k : ℕ) (ht : 1 ≤ t) (hfactor : 0 < factor)
    (hp : 1 / t ^ b ≤ p) (hpower : t ^ d ≤ u ^ c) (hgap : b * k + 1 ≤ d)
    (hconstant : factor ≤ tau * t) :
    n / u ^ c ≤ p ^ k * tau * n / factor := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hupos : 0 < u ^ c := (pow_pos htpos _).trans_le hpower
  have hmass : t ≤ p ^ k * u ^ c := by
    simpa only [pow_one] using inversePower_density_ge_power t p (u ^ c) b k 1 d ht hp hgap hpower
  apply (le_div_iff₀ hfactor).mpr
  calc
    _ ≤ (n / u ^ c) * (tau * t) := mul_le_mul_of_nonneg_left hconstant zero_le
    _ ≤ (n / u ^ c) * (tau * (p ^ k * u ^ c)) := by gcongr
    _ = _ := by field_simp

theorem crossScale_uniform_coefficient_small
    (t u p C tau : ℝ≥0) (b : ℕ) (ht : 1 ≤ t) (hb : 2 ≤ b)
    (hu : u ≤ t) (hp : p ≤ 2 / t ^ b) (hconstant : 2 * C ≤ tau * t) :
    C * u * p ≤ tau := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hp' : p ≤ 2 / t ^ 2 := hp.trans
    (div_le_div_of_nonneg_left zero_le (pow_pos htpos _) (pow_le_pow_right₀ ht hb))
  calc
    _ ≤ C * t * (2 / t ^ 2) := mul_le_mul (mul_le_mul_of_nonneg_left hu zero_le) hp' zero_le zero_le
    _ = (2 * C) / t := by field_simp
    _ ≤ tau := (div_le_iff₀ htpos).mpr hconstant

theorem ksssDensityHorizon_survival_upper
    (E u : ℝ) (c : ℕ) (hE : 0 < E) (hu : 1 ≤ u) (hedge : 3 * u ^ c ≤ E) :
    ksssEdgeDensity E (ksssDensityHorizon E (1 / u ^ c)) ≤ 2 / u ^ c := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have huc : 0 < u ^ c := pow_pos hu0 _
  have hbound := (ksssDensityHorizon_bounds E (1 / u ^ c) hE (by positivity)
    ((div_le_one huc).mpr (one_le_pow₀ hu))).2.2
  have hthree : 3 ≤ E / u ^ c := (le_div_iff₀ huc).mpr hedge
  unfold ksssEdgeDensity
  calc
    _ ≤ (E / u ^ c + 3) / E := div_le_div_of_nonneg_right (by simpa only [mul_one_div] using hbound.le) hE.le
    _ ≤ (E / u ^ c + E / u ^ c) / E := div_le_div_of_nonneg_right (add_le_add le_rfl hthree) hE.le
    _ = _ := by field_simp; ring

theorem ksssDensityHorizon_survival_common_scale_upper
    (E u t : ℝ) (c d : ℕ) (hE : 0 < E) (hu : 1 ≤ u) (ht : 0 < t)
    (hedge : 3 * u ^ c ≤ E) (hpower : t ^ d ≤ u ^ c) :
    ksssEdgeDensity E (ksssDensityHorizon E (1 / u ^ c)) ≤ 2 / t ^ d :=
  (ksssDensityHorizon_survival_upper E u c hE hu hedge).trans
    (div_le_div_of_nonneg_left (by norm_num) (pow_pos ht _) hpower)

end Erdos207
