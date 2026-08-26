import ErdosProblems.Erdos117.LogScale

/-!
# Numerical envelope for the constructed cover

This file bounds a numerical error function. It does not supply or assume
any group-theoretic theorem about the derived-subgroup order.
-/

namespace Erdos117

open Filter
open scoped Topology

noncomputable def finiteCoverError (n q : ℕ) : ℝ :=
  96 * Real.sqrt n * ((q : ℝ) + Nat.clog 2 ((2 * n) ^ 2) + 1) *
    Real.sqrt ((q : ℝ) + Nat.clog 2 ((2 * n) ^ 2) + 1) +
  (2 * (q : ℝ) + (q : ℝ) * q * Nat.clog 2 ((2 * n) ^ 2)) * Nat.log 2 n +
  (q : ℝ) ^ 2 * Real.log 2 + Real.log (coverExtensionPolynomial n)

noncomputable def errorCoefficient (A : ℕ) : ℝ :=
  96 * ((A : ℝ) + 5) * Real.sqrt ((A : ℝ) + 5) + 2 * A + 5 * (A : ℝ) ^ 2 + 11

theorem errorCoefficient_nonneg (A : ℕ) : 0 ≤ errorCoefficient A := by
  unfold errorCoefficient
  positivity

/-- The explicit error is controlled by a square-root term and a sixth
power of the logarithmic scale. The inputs are only natural numbers. -/
theorem finiteCoverError_le_envelope {n q A : ℕ} (hn : 1 ≤ n)
    (hq : q ≤ A * logScale n ^ 2) :
    finiteCoverError n q ≤
      96 * ((A : ℝ) + 5) * Real.sqrt ((A : ℝ) + 5) * Real.sqrt n * (logScale n : ℝ) ^ 3 +
      (2 * (A : ℝ) + 5 * (A : ℝ) ^ 2 + 11) * (logScale n : ℝ) ^ 6 := by
  let T : ℝ := logScale n
  have hT : 1 ≤ T := by
    dsimp [T]
    exact_mod_cast (Nat.succ_le_of_lt (logScale_pos n))
  have hT0 : 0 ≤ T := by linarith
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hq' : (q : ℝ) ≤ A * T ^ 2 := by dsimp [T]; exact_mod_cast hq
  have hell : (Nat.clog 2 ((2 * n) ^ 2) : ℝ) ≤ 4 * T := by
    dsimp [T]
    exact_mod_cast conjugacy_clog_le_logScale n
  have hfloor : (Nat.log 2 n : ℝ) ≤ T := by
    dsimp [T]
    exact_mod_cast floor_log_le_logScale n
  have hH : (q : ℝ) + Nat.clog 2 ((2 * n) ^ 2) + 1 ≤ ((A : ℝ) + 5) * T ^ 2 := by
    have hT2 : T ≤ T ^ 2 := by nlinarith only [hT]
    nlinarith only [hq', hell, hT2, hT]
  have hroot : Real.sqrt ((q : ℝ) + Nat.clog 2 ((2 * n) ^ 2) + 1) ≤
      Real.sqrt ((A : ℝ) + 5) * T := by
    calc
      _ ≤ Real.sqrt (((A : ℝ) + 5) * T ^ 2) := Real.sqrt_le_sqrt hH
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hT0]
  have hlarge :
      96 * Real.sqrt n * ((q : ℝ) + Nat.clog 2 ((2 * n) ^ 2) + 1) *
        Real.sqrt ((q : ℝ) + Nat.clog 2 ((2 * n) ^ 2) + 1) ≤
      96 * ((A : ℝ) + 5) * Real.sqrt ((A : ℝ) + 5) * Real.sqrt n * T ^ 3 := by
    calc
      _ ≤ 96 * Real.sqrt n * (((A : ℝ) + 5) * T ^ 2) *
          (Real.sqrt ((A : ℝ) + 5) * T) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hH (by positivity)) hroot
          (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have htail : (2 * (q : ℝ) + (q : ℝ) * q * Nat.clog 2 ((2 * n) ^ 2)) * Nat.log 2 n ≤
      2 * (A : ℝ) * T ^ 3 + 4 * (A : ℝ) ^ 2 * T ^ 6 := by
    calc
      _ ≤ (2 * ((A : ℝ) * T ^ 2) + ((A : ℝ) * T ^ 2) * ((A : ℝ) * T ^ 2) *
          (4 * T)) * T := by gcongr
      _ = _ := by ring
  have hqlog : (q : ℝ) ^ 2 * Real.log 2 ≤ (A : ℝ) ^ 2 * T ^ 4 := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    calc
      _ ≤ ((A : ℝ) * T ^ 2) ^ 2 * 1 := by
        exact mul_le_mul (pow_le_pow_left₀ hq0 hq' 2) hlog2
          (Real.log_natCast_nonneg 2) (by positivity)
      _ = _ := by ring
  have hpow3 : T ^ 3 ≤ T ^ 6 := pow_le_pow_right₀ hT (by decide)
  have hpow4 : T ^ 4 ≤ T ^ 6 := pow_le_pow_right₀ hT (by decide)
  have hpow1 : T ≤ T ^ 6 := by simpa only [pow_one] using pow_le_pow_right₀ hT (by decide : 1 ≤ 6)
  have hsmall3 := mul_le_mul_of_nonneg_left hpow3 (show 0 ≤ 2 * (A : ℝ) by positivity)
  have hsmall4 := mul_le_mul_of_nonneg_left hpow4 (show 0 ≤ (A : ℝ) ^ 2 by positivity)
  have hpoly : Real.log (coverExtensionPolynomial n) ≤ 11 * T ^ 6 :=
    (log_coverExtensionPolynomial_le hn).trans (mul_le_mul_of_nonneg_left hpow1 (by norm_num))
  unfold finiteCoverError
  change _ ≤ 96 * ((A : ℝ) + 5) * Real.sqrt ((A : ℝ) + 5) * Real.sqrt n * T ^ 3 +
    (2 * (A : ℝ) + 5 * (A : ℝ) ^ 2 + 11) * T ^ 6
  nlinarith only [hlarge, htail, hqlog, hsmall3, hsmall4, hpoly]

theorem finiteCoverError_le_sqrt_cube {n q A : ℕ} (hn : 1 ≤ n)
    (hq : q ≤ A * logScale n ^ 2) (hgrowth : (logScale n : ℝ) ^ 3 ≤ Real.sqrt n) :
    finiteCoverError n q ≤ errorCoefficient A * Real.sqrt n * (logScale n : ℝ) ^ 3 := by
  have h := finiteCoverError_le_envelope hn hq
  have hnonneg : 0 ≤ 2 * (A : ℝ) + 5 * (A : ℝ) ^ 2 + 11 := by positivity
  have htail := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hgrowth (show 0 ≤ (logScale n : ℝ) ^ 3 by positivity)) hnonneg
  unfold errorCoefficient
  nlinarith only [h, htail]

/-- Uniform eventual control of the numerical error for every `q` in a
quadratic logarithmic range. No assertion that a group satisfies that range
is made here. -/
theorem eventually_finiteCoverError_le (A : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q ≤ A * logScale n ^ 2 →
      finiteCoverError n q ≤ errorCoefficient A * Real.sqrt n * (logScale n : ℝ) ^ 3 := by
  filter_upwards [eventually_ge_atTop 1, eventually_logScale_cube_le_sqrt] with n hn hgrowth
  intro q hq
  exact finiteCoverError_le_sqrt_cube hn hq hgrowth

/-- The numerical envelope has precisely the logarithmic scale used in
the claimed theorem. -/
theorem eventually_finiteCoverError_le_log (A : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q ≤ A * logScale n ^ 2 →
      finiteCoverError n q ≤
        (errorCoefficient A * (2 / Real.log 2) ^ 3) *
          Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 := by
  filter_upwards [eventually_finiteCoverError_le A] with n hn
  intro q hq
  calc
    _ ≤ errorCoefficient A * Real.sqrt n * (logScale n : ℝ) ^ 3 := hn q hq
    _ ≤ errorCoefficient A * Real.sqrt n *
        ((2 / Real.log 2) * Real.log ((n : ℝ) + 2)) ^ 3 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (logScale_le_log n) 3)
        (mul_nonneg (errorCoefficient_nonneg A) (Real.sqrt_nonneg _))
    _ = _ := by ring

end Erdos117
