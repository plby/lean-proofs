import ErdosProblems.Erdos4.TiltedActualSieve
import ErdosProblems.Erdos4.TiltedGeometricBudget

/-! Uniform error budgets at the actual composite parameters, before choosing the fiber partitions. -/

namespace Erdos4.Tilted

open Filter

theorem eventually_offset_le_smallCutoff :
    ∀ᶠ x : ℕ in atTop, offsetLimit x ≤ smallCutoff x := by
  filter_upwards [eventually_smallCutoff_bounds, eventually_outerScale_bounds] with x hw hb
  have hL : 1 ≤ Real.log (x : ℝ) := by linarith [hb.1]
  have hU := (offsetLimit_bounds hL).2
  have hW := hw.2.2.2.2.2.2.2
  have hh : (offsetLimit x : ℝ) ≤ smallCutoff x := by linarith
  exact_mod_cast hh

theorem eventually_actual_gcd_error {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ (b V : ℝ) (M : ℕ),
      0 ≤ b → b ≤ Real.log (x : ℝ) ^ (2 : ℕ) / x → M ≤ 17 * x →
      0 ≤ V → V ≤ 2 * (offsetLimit x : ℝ) →
      gcdTiltError (smallCutoff x) (Nat.sqrt x) (gapTarget c x ^ blockSize x (compositeTargets c x))
        (tiltExponent x) ((b * ((M : ℝ) + x)) ^ 2) (V ^ 2) ≤
        1 / Real.log (x : ℝ) ^ (40 : ℕ) := by
  filter_upwards [eventually_gcdTiltError_budget, eventually_smallCutoff_bounds,
    eventually_actual_block_weight_bounds hc (by norm_num : (0 : ℝ) < 1 / 16),
    eventually_outerScale_bounds, log_tendsto.eventually (eventually_ge_atTop 324),
    eventually_ge_atTop 16] with x he hw hweights hb hL hx
  intro b V M hb0 hble hM hV0 hV
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hL1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hU := offsetLimit_bounds hL1
  have hcoeff := divisor_coefficient_budget hL hxpos hb0 hble (Nat.cast_nonneg M)
    (by exact_mod_cast hM) (Nat.cast_nonneg (offsetLimit x)) hU.2
  have hVpow : V ^ 2 ≤ Real.log (x : ℝ) ^ (3 : ℕ) :=
    (pow_le_pow_left₀ hV0 hV 2).trans hcoeff.2
  exact he (smallCutoff x) (Nat.sqrt x) (gapTarget c x ^ blockSize x (compositeTargets c x))
    (tiltExponent x) ((b * ((M : ℝ) + x)) ^ 2) (V ^ 2)
    hw.2.2.1 (rpow_quarter_le_nat_sqrt hx) (hweights hb.2.2.2.2.2.2.1.le).1
    (sq_nonneg _) hcoeff.1 (sq_nonneg V) hVpow

theorem eventually_actual_correlation_budgets {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      let K := (blockSize x (compositeTargets c x) : ℝ)
      let Y := gapTarget c x
      let w := (smallCutoff x : ℝ)
      (2 + 8 * K) * (2 * K) ^ 2 * Real.log Y / (w * Real.log 2) ≤
          1 / Real.log (x : ℝ) ^ (40 : ℕ) ∧
        8 * (K + 1) * (2 * K) ^ 2 * Real.log Y / (w * Real.log 2) ≤
          1 / Real.log (x : ℝ) ^ (40 : ℕ) := by
  filter_upwards [eventually_blockSize_le_log hc, eventually_smallCutoff_bounds,
    eventually_gapTarget_bounds hc, eventually_outerScale_bounds,
    log_tendsto.eventually (eventually_ge_atTop (128 / Real.log 2))]
    with x hK hw hY hb hcoef
  have hL : 1 ≤ Real.log (x : ℝ) := by linarith [hb.1]
  have hpower : Real.log (x : ℝ) ≤ Real.log (x : ℝ) ^ (54 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (by norm_num : 1 ≤ (54 : ℕ))
  have hlogY : Real.log (gapTarget c x : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    have hh := Real.log_le_log (by exact_mod_cast hY.1 : (0 : ℝ) < gapTarget c x)
      (by exact_mod_cast hY.2.2.2.1 : (gapTarget c x : ℝ) ≤ (x : ℝ) ^ 2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  exact block_correlation_log_budgets hL hw.2.2.1 (Nat.cast_nonneg _) hK
    (Real.log_natCast_nonneg _) hlogY (hcoef.trans hpower)

end Erdos4.Tilted
