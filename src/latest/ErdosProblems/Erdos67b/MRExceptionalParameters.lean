import ErdosProblems.Erdos67b.MRExceptionalSamples

/-!
# Choosing the moment order in the exceptional sample count

This is the explicit scalar optimization of the prime-line sampled
moment. Factorial and endpoint costs remain visible. Uniform estimates
after selecting the final scheduled block are still a further step.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

theorem mrCeil_logRatio_bounds {T v : ℝ} (hT : 1 ≤ T) (hv : 0 < v) :
    Real.log T ≤ (⌈Real.log T / v⌉₊ : ℝ) * v ∧
      (⌈Real.log T / v⌉₊ : ℝ) * v ≤ Real.log T + v := by
  have hratio : 0 ≤ Real.log T / v := div_nonneg (Real.log_nonneg hT) hv.le
  constructor
  · exact (div_le_iff₀ hv).mp (Nat.le_ceil (Real.log T / v))
  · have hh := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hratio) hv
    have heq : (Real.log T / v + 1) * v = Real.log T + v := by field_simp
    rw [heq] at hh
    exact hh.le

/-- Explicit cancellation of the scale in a sampled prime moment. -/
theorem mrPrimeLineSampleBudget_le_exponential
    {L N k : ℕ} (hN : 0 < N) {T v alpha : ℝ}
    (hT : 1 ≤ T) (hv : 0 ≤ v) (halpha : 0 ≤ alpha)
    (hL : Real.exp v ≤ L) (hNhi : (N : ℝ) ≤ Real.exp (v + 1))
    (hklo : Real.log T ≤ (k : ℝ) * v) (hkhi : (k : ℝ) * v ≤ Real.log T + v) :
    mrPrimeLineSampleBudget L N k T (Real.exp (-alpha * v)) ≤
      (4 + 2 * Real.pi) * (3 + 2 * (k : ℝ) * (v + 1)) *
        (2 * Real.exp 1 * (k : ℝ)) ^ k * Real.exp (2 * alpha * (Real.log T + v)) := by
  have hLpos : (0 : ℝ) < L := (Real.exp_pos v).trans_le hL
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlogNhi : Real.log N ≤ v + 1 := by
    have hh := Real.log_le_log (by exact_mod_cast hN : (0 : ℝ) < N) hNhi
    simpa only [Real.log_exp] using hh
  have hlogpow : Real.log (N ^ k : ℕ) ≤ (k : ℝ) * (v + 1) := by
    rw [Nat.cast_pow, Real.log_pow]
    exact mul_le_mul_of_nonneg_left hlogNhi (Nat.cast_nonneg k)
  have hNpow : ((N ^ k : ℕ) : ℝ) ≤ Real.exp ((k : ℝ) * (v + 1)) := by
    calc
      _ = (N : ℝ) ^ k := Nat.cast_pow N k
      _ ≤ (Real.exp (v + 1)) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg N) hNhi k
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hTexp : T ≤ Real.exp ((k : ℝ) * (v + 1)) := by
    calc
      T = Real.exp (Real.log T) := (Real.exp_log (by linarith : 0 < T)).symm
      _ ≤ Real.exp ((k : ℝ) * v) := Real.exp_le_exp.mpr hklo
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ k by positivity])
  have hexp1 : 1 ≤ Real.exp ((k : ℝ) * (v + 1)) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have htime : 2 * (T + 1) + 2 * Real.pi * (N ^ k : ℕ) ≤
      (4 + 2 * Real.pi) * Real.exp ((k : ℝ) * (v + 1)) := by
    nlinarith [Real.pi_pos]
  have hmass : (2 / (L : ℝ)) ^ k ≤ (2 * Real.exp (-v)) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    calc
      2 / (L : ℝ) ≤ 2 / Real.exp v := div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos v) hL
      _ = _ := by rw [div_eq_mul_inv, ← Real.exp_neg]
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  have hthreshold : (Real.exp (-alpha * v) ^ (2 * k))⁻¹ =
      Real.exp (2 * alpha * ((k : ℝ) * v)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  have hthresholdle : Real.exp (2 * alpha * ((k : ℝ) * v)) ≤
      Real.exp (2 * alpha * (Real.log T + v)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkhi (by positivity))
  have hlogpow0 : 0 ≤ Real.log (N ^ k : ℕ) := Real.log_nonneg (by exact_mod_cast pow_pos hN k)
  have hlogfactor : 3 + 2 * Real.log (N ^ k : ℕ) ≤ 3 + 2 * (k : ℝ) * (v + 1) := by nlinarith
  calc
    mrPrimeLineSampleBudget L N k T (Real.exp (-alpha * v)) =
        (3 + 2 * Real.log (N ^ k : ℕ)) * (2 * (T + 1) + 2 * Real.pi * (N ^ k : ℕ)) *
          ((k.factorial : ℝ) * (2 / (L : ℝ)) ^ k) * Real.exp (2 * alpha * ((k : ℝ) * v)) := by
      unfold mrPrimeLineSampleBudget
      rw [div_eq_mul_inv, hthreshold]
    _ ≤ (3 + 2 * (k : ℝ) * (v + 1)) *
        ((4 + 2 * Real.pi) * Real.exp ((k : ℝ) * (v + 1))) *
          ((k : ℝ) ^ k * (2 * Real.exp (-v)) ^ k) * Real.exp (2 * alpha * (Real.log T + v)) := by
      have hfirst := mul_le_mul hlogfactor htime (by positivity) (by positivity)
      have hsecond := mul_le_mul hfac hmass (by positivity) (by positivity)
      have hnum := mul_le_mul hfirst hsecond (by positivity) (by positivity)
      exact mul_le_mul hnum hthresholdle (by positivity) (by positivity)
    _ = _ := by
      have heq : Real.exp ((k : ℝ) * (v + 1)) * (2 * Real.exp (-v)) ^ k =
          (2 * Real.exp 1) ^ k := by
        rw [mul_pow, ← Real.exp_nat_mul]
        calc
          _ = 2 ^ k * (Real.exp ((k : ℝ) * (v + 1)) * Real.exp ((k : ℝ) * (-v))) := by ring
          _ = 2 ^ k * Real.exp (k : ℝ) := by rw [← Real.exp_add]; congr 2; ring
          _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring
      calc
        _ = (4 + 2 * Real.pi) * (3 + 2 * (k : ℝ) * (v + 1)) * (k : ℝ) ^ k *
            (Real.exp ((k : ℝ) * (v + 1)) * (2 * Real.exp (-v)) ^ k) *
              Real.exp (2 * alpha * (Real.log T + v)) := by ring
        _ = _ := by rw [heq, mul_pow]; ring

theorem mrPrimeLineSampleBudget_ceil_le
    {L N : ℕ} (hN : 0 < N) {T v alpha : ℝ}
    (hT : 1 ≤ T) (hv : 0 < v) (halpha : 0 ≤ alpha)
    (hL : Real.exp v ≤ L) (hNhi : (N : ℝ) ≤ Real.exp (v + 1)) :
    mrPrimeLineSampleBudget L N ⌈Real.log T / v⌉₊ T (Real.exp (-alpha * v)) ≤
      (4 + 2 * Real.pi) * (3 + 2 * (⌈Real.log T / v⌉₊ : ℝ) * (v + 1)) *
        (2 * Real.exp 1 * (⌈Real.log T / v⌉₊ : ℝ)) ^ ⌈Real.log T / v⌉₊ *
          Real.exp (2 * alpha * (Real.log T + v)) := by
  have hk := mrCeil_logRatio_bounds hT hv
  exact mrPrimeLineSampleBudget_le_exponential hN hT hv.le halpha hL hNhi hk.1 hk.2

noncomputable section

/-- The explicit exponential budget after optimizing the integer moment order. -/
def mrOptimizedPrimeSampleBudget (T v alpha : ℝ) : ℝ :=
  (4 + 2 * Real.pi) * (3 + 2 * (⌈Real.log T / v⌉₊ : ℝ) * (v + 1)) *
    (2 * Real.exp 1 * (⌈Real.log T / v⌉₊ : ℝ)) ^ ⌈Real.log T / v⌉₊ *
      Real.exp (2 * alpha * (Real.log T + v))

/-- The actual scheduled exceptional class, with moment orders chosen
from each subblock's logarithmic scale and no endpoint assumptions left. -/
theorem mrArithmetic_noSmall_sample_card_le_optimized
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hU : ∀ t ∈ S, t ∈ mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J) :
    (S.card : ℝ) ≤ ∑ r ∈ mrScheduledSubblocks eta p₁ q₁ j,
      mrOptimizedPrimeSampleBudget T (mrScheduledParameter eta p₁ q₁ j r)
        (mrThresholdExponent eta (j : ℝ)) := by
  have hH1 := mrLogSchedule_resolution_one_le heta1 (by linarith : 0 ≤ p₁) hlogq hbudget hj
  have hH0 : 0 < mrLogBlockResolution eta p₁ q₁ (j : ℝ) := by linarith
  have hbeta : 0 ≤ mrThresholdExponent eta (j : ℝ) :=
    (mrThresholdExponent_bounds heta0.le (by linarith) (by exact_mod_cast hj)).1
  have hbase := mrArithmetic_noSmall_sample_card_le eta p₁ q₁ hj hjJ
    (fun r ↦ ⌈Real.log T / mrScheduledParameter eta p₁ q₁ j r⌉₊)
    hbound S (by linarith : 0 ≤ T) hST hsep hU
  apply hbase.trans
  apply Finset.sum_le_sum
  intro r hr
  have hparam := mrScheduledParameter_bounds heta1 hp hq hlogq hbudget hj hr
  have hpj := mrLogScheduleLower_ge (by linarith : 0 ≤ p₁) hq hj
  have hv : 0 < mrScheduledParameter eta p₁ q₁ j r := by linarith
  exact mrPrimeLineSampleBudget_ceil_le (mrNarrowPrimeInterval_upper_pos hH0 r) hT hv hbeta
    (Nat.le_ceil _) (mrNarrowPrimeInterval_upper_le_exp_shift hH1 r)

end

end Erdos67b
