/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPowerExponentChoice

/-! # Scaling the mathematical hierarchy preserves a uniform physical decay exponent -/

namespace Erdos207

theorem ksssPowerDenominatorExponent_scale_le (q b B k Rmin c : ℕ) (hc : 1 ≤ c) :
    ksssPowerDenominatorExponent q (b * c) B (k * c) (Rmin * c) ≤
      ksssPowerDenominatorExponent q b B k Rmin * c := by
  have herror : ksssPowerErrorExponent (b * c) B ≤ ksssPowerErrorExponent b B * c := by
    unfold ksssPowerErrorExponent
    nlinarith
  have hmargin : ksssPowerMarginExponent q (b * c) B ≤ ksssPowerMarginExponent q b B * c := by
    unfold ksssPowerMarginExponent
    nlinarith
  have hdet : ksssPowerDeterministicExponent (b * c) ≤ ksssPowerDeterministicExponent b * c := by
    unfold ksssPowerDeterministicExponent
    nlinarith
  have hraw : ksssPowerRawVarianceExponent (b * c) (k * c) ≤ ksssPowerRawVarianceExponent b k * c := by
    unfold ksssPowerRawVarianceExponent
    nlinarith
  have hjump : ksssPowerJumpExponent (b * c) (k * c) ≤ ksssPowerJumpExponent b k * c := by
    have hk := le_max_left (k + 2) (ksssPowerDeterministicExponent b)
    have hd := le_max_right (k + 2) (ksssPowerDeterministicExponent b)
    have hk' := Nat.mul_le_mul_right c hk
    have hd' := Nat.mul_le_mul_right c hd
    have hm : max (k * c + 2) (ksssPowerDeterministicExponent (b * c)) ≤
        max (k + 2) (ksssPowerDeterministicExponent b) * c :=
      max_le (by nlinarith) (hdet.trans hd')
    unfold ksssPowerJumpExponent
    nlinarith
  have hvariance : ksssPowerVarianceExponent (b * c) (k * c) ≤ ksssPowerVarianceExponent b k * c := by
    have hv := le_max_left (ksssPowerRawVarianceExponent b k) (2 * ksssPowerDeterministicExponent b)
    have hd := le_max_right (ksssPowerRawVarianceExponent b k) (2 * ksssPowerDeterministicExponent b)
    have hv' := Nat.mul_le_mul_right c hv
    have hd' := Nat.mul_le_mul_right c hd
    have hm : max (ksssPowerRawVarianceExponent (b * c) (k * c))
        (2 * ksssPowerDeterministicExponent (b * c)) ≤
        max (ksssPowerRawVarianceExponent b k) (2 * ksssPowerDeterministicExponent b) * c :=
      max_le (hraw.trans hv') (by nlinarith)
    unfold ksssPowerVarianceExponent
    nlinarith
  have htheta : ksssPowerThetaExponent q (b * c) B (k * c) ≤ ksssPowerThetaExponent q b B k * c := by
    unfold ksssPowerThetaExponent
    nlinarith
  unfold ksssPowerDenominatorExponent
  nlinarith

theorem ksss_physical_exponent_uniform_lower (q b B k Rmin c : ℕ) (hc : 1 ≤ c) :
    1 / (ksssPowerDenominatorExponent q b B k Rmin : ℝ) ≤
      (c : ℝ) / (ksssPowerDenominatorExponent q (b * c) B (k * c) (Rmin * c) : ℝ) := by
  have hbase : 0 < ksssPowerDenominatorExponent q b B k Rmin := by
    unfold ksssPowerDenominatorExponent
    omega
  have hscaled : 0 < ksssPowerDenominatorExponent q (b * c) B (k * c) (Rmin * c) := by
    unfold ksssPowerDenominatorExponent
    omega
  apply (div_le_div_iff₀ (by exact_mod_cast hbase) (by exact_mod_cast hscaled)).mpr
  simpa only [one_mul, mul_one, mul_comm] using
    (show (ksssPowerDenominatorExponent q (b * c) B (k * c) (Rmin * c) : ℝ) ≤
      (ksssPowerDenominatorExponent q b B k Rmin : ℝ) * c by
        exact_mod_cast ksssPowerDenominatorExponent_scale_le q b B k Rmin c hc)

end Erdos207
