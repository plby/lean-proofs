import ErdosProblems.Erdos4.FGKMTGrowingNormalizationBudget
import ErdosProblems.Erdos4.FGKMTLogarithmicAbsorption

/-! Fixed powers of the small modulus are absorbed by the proved exponential saving. -/

namespace Erdos4.FGKMT

open Filter

theorem eventually_smallPresieve_pow_le_exp (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop, ∀ B : ℕ,
      (smallPresieveModulus (growingPrecutoff x) B : ℝ) ^ m ≤
        Real.exp (a * Real.sqrt (Real.log (x : ℝ))) := by
  have hlogTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hvTop := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hlogTop
  filter_upwards [eventually_growingPrecutoff_bounds,
    hvTop.eventually (eventually_ge_atTop ((m : ℝ) * Real.log 4 / a)),
    hlogTop.eventually (eventually_ge_atTop 1)] with x hD hlarge hlog
  change 1 ≤ Real.log (x : ℝ) at hlog
  let v := Real.log (x : ℝ) ^ (1 / 4 : ℝ)
  have hv : 0 ≤ v := Real.rpow_nonneg (Real.log_natCast_nonneg x) _
  change (m : ℝ) * Real.log 4 / a ≤ v at hlarge
  have hlin : (m : ℝ) * Real.log 4 ≤ a * v := by
    have hh := (div_le_iff₀ ha).mp hlarge
    nlinarith
  have hvsq : v ^ 2 = Real.sqrt (Real.log (x : ℝ)) := by
    dsimp only [v]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_natCast_nonneg x), Real.sqrt_eq_rpow]
    norm_num
  intro B
  have hMpos : (0 : ℝ) < smallPresieveModulus (growingPrecutoff x) B := by
    exact_mod_cast smallPresieveModulus_pos (growingPrecutoff x) B
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hMlog : Real.log (smallPresieveModulus (growingPrecutoff x) B : ℝ) ≤ Real.log 4 * v :=
    (log_smallPresieveModulus_le (growingPrecutoff x) B).trans
      (mul_le_mul_of_nonneg_left hD.2.2 hlog4)
  have hexponent : (m : ℝ) * Real.log (smallPresieveModulus (growingPrecutoff x) B : ℝ) ≤
      a * Real.sqrt (Real.log (x : ℝ)) := by
    calc
      _ ≤ (m : ℝ) * (Real.log 4 * v) := mul_le_mul_of_nonneg_left hMlog (Nat.cast_nonneg m)
      _ = ((m : ℝ) * Real.log 4) * v := by ring
      _ ≤ (a * v) * v := mul_le_mul_of_nonneg_right hlin hv
      _ = a * Real.sqrt (Real.log (x : ℝ)) := by rw [← hvsq]; ring
  calc
    _ = Real.exp ((m : ℝ) * Real.log (smallPresieveModulus (growingPrecutoff x) B : ℝ)) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hMpos m)]
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

theorem eventually_smallPresieve_cubic_decay {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) :
    ∀ᶠ x : ℕ in atTop, ∀ B : ℕ,
      2 * (smallPresieveModulus (growingPrecutoff x) B : ℝ) ^ 3 * C *
        Real.log (x : ℝ) ^ 3 * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ))) ≤ 1 := by
  filter_upwards [eventually_smallPresieve_pow_le_exp 3 (show 0 < a / 4 by positivity),
    eventually_const_mul_sqrtLog_pow_le_exp 6 (2 * C) (show 0 < a / 4 by positivity)]
    with x hM hpoly
  intro B
  have hsix : Real.sqrt (Real.log (x : ℝ)) ^ 6 = Real.log (x : ℝ) ^ 3 := by
    calc
      _ = (Real.sqrt (Real.log (x : ℝ)) ^ 2) ^ 3 := by ring
      _ = _ := by rw [Real.sq_sqrt (Real.log_natCast_nonneg x)]
  rw [hsix] at hpoly
  have hmul := mul_le_mul (hM B) hpoly
    (mul_nonneg (by linarith : 0 ≤ 2 * C) (pow_nonneg (Real.log_natCast_nonneg x) 3))
    (Real.exp_pos _).le
  have hexp : Real.exp ((a / 4) * Real.sqrt (Real.log (x : ℝ))) *
      Real.exp ((a / 4) * Real.sqrt (Real.log (x : ℝ))) *
      Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ))) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring_nf
  have hh := mul_le_mul_of_nonneg_right hmul (Real.exp_pos
    (-(a / 2) * Real.sqrt (Real.log (x : ℝ)))).le
  rw [hexp] at hh
  exact (show _ = (smallPresieveModulus (growingPrecutoff x) B : ℝ) ^ 3 *
      (2 * C * Real.log (x : ℝ) ^ 3) *
      Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ))) by ring).trans_le hh

end Erdos4.FGKMT
