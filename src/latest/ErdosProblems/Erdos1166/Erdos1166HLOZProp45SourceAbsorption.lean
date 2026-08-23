/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZProp45SourceEndpoints
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Parameters
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma411

/-!
# Absorbing the Proposition 4.5 branch errors

The checked finite conditional core of HLOZ Proposition 4.5 produces four
stretched-exponential branches: four copies of `exp (-m^(8/25))` and two
copies of `exp (-sqrt m)`.  This file verifies that their sum is eventually
bounded by the exact cubic inverse-power exceptional scale used by the
Proposition-4.7 assembly.
-/

namespace Erdos1166.HLOZProp45SourceAbsorption

open Filter
open scoped ENNReal

open HLOZPairing.ScreeningBridge HLOZProp47Parameters
open HLOZProp45SourceClock HLOZProp45SourceEndpoints
open HLOZLemma411 HLOZScreeningAssembly

/-- A positive power `m^a`, for `a ≤ 1`, eventually dominates
`log (m+1)^2`.  The shifted logarithm is the one appearing in the exact
Proposition-4.7 exceptional scale. -/
lemma eventually_log_add_one_sq_le_nat_rpow
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∀ᶠ m : ℕ in atTop,
      Real.log ((m : ℝ) + 1) ^ 2 ≤ (m : ℝ) ^ a := by
  have hraw := (tendsto_add_atTop_nat 1).eventually
    (eventually_const_mul_log_sq_le_rpow
      (c := (1 : ℝ)) (c₁ := (1 : ℝ) / 2) (a := a)
      (by norm_num) (by norm_num) ha0)
  have htwo : (2 : ℝ) ^ a ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha1
    simpa only [Real.rpow_one] using this
  filter_upwards [hraw, eventually_ge_atTop 1] with m hraw hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hbase : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast (show m + 1 ≤ 2 * m by omega)
  have hrpow : (((m + 1 : ℕ) : ℝ)) ^ a ≤
      (2 * (m : ℝ)) ^ a := Real.rpow_le_rpow (by positivity) hbase ha0.le
  calc
    Real.log ((m : ℝ) + 1) ^ 2 =
        Real.log (((m + 1 : ℕ) : ℝ)) ^ 2 := by norm_num
    _ ≤ (1 / 2 : ℝ) * (((m + 1 : ℕ) : ℝ)) ^ a := by
      simpa only [one_mul] using hraw
    _ ≤ (1 / 2 : ℝ) * (2 * (m : ℝ)) ^ a := by gcongr
    _ = (1 / 2 : ℝ) * ((2 : ℝ) ^ a * (m : ℝ) ^ a) := by
      rw [Real.mul_rpow (by norm_num) hm0]
    _ ≤ (1 / 2 : ℝ) * (2 * (m : ℝ) ^ a) := by gcongr
    _ = (m : ℝ) ^ a := by ring

/-- Fixed multiples of the shifted logarithmic square are absorbed by the
same positive power.  This strengthened form is used when a polynomial
number of interval-level Proposition-4.5 errors is inserted into the
Proposition-4.8 recursion. -/
lemma eventually_const_mul_log_add_one_sq_le_nat_rpow
    {c a : ℝ} (hc : 0 < c) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∀ᶠ m : ℕ in atTop,
      c * Real.log ((m : ℝ) + 1) ^ 2 ≤ (m : ℝ) ^ a := by
  have hraw := (tendsto_add_atTop_nat 1).eventually
    (eventually_const_mul_log_sq_le_rpow
      (c := c) (c₁ := (1 : ℝ) / 2) (a := a)
      hc (by norm_num) ha0)
  have htwo : (2 : ℝ) ^ a ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha1
    simpa only [Real.rpow_one] using this
  filter_upwards [hraw, eventually_ge_atTop 1] with m hraw hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hbase : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast (show m + 1 ≤ 2 * m by omega)
  have hrpow : (((m + 1 : ℕ) : ℝ)) ^ a ≤
      (2 * (m : ℝ)) ^ a := Real.rpow_le_rpow (by positivity) hbase ha0.le
  calc
    c * Real.log ((m : ℝ) + 1) ^ 2 =
        c * Real.log (((m + 1 : ℕ) : ℝ)) ^ 2 := by norm_num
    _ ≤ (1 / 2 : ℝ) * (((m + 1 : ℕ) : ℝ)) ^ a := hraw
    _ ≤ (1 / 2 : ℝ) * (2 * (m : ℝ)) ^ a := by gcongr
    _ = (1 / 2 : ℝ) * ((2 : ℝ) ^ a * (m : ℝ) ^ a) := by
      rw [Real.mul_rpow (by norm_num) hm0]
    _ ≤ (1 / 2 : ℝ) * (2 * (m : ℝ) ^ a) := by gcongr
    _ = (m : ℝ) ^ a := by ring

private theorem eventually_source_error_real_le_exceptional :
    ∀ᶠ m : ℕ in atTop,
      Real.exp (-sourceRate m) ≤
          ((m : ℝ) + 1) ^ (-(3 * kappa)) ∧
        Real.exp (-Real.sqrt (m : ℝ)) ≤
          ((m : ℝ) + 1) ^ (-(3 * kappa)) := by
  have hrate := eventually_log_add_one_sq_le_nat_rpow
    (a := (8 : ℝ) / 25) (by norm_num) (by norm_num)
  have hsqrt := eventually_log_add_one_sq_le_nat_rpow
    (a := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  have habsorb := (tendsto_add_atTop_nat 1).eventually
    (eventually_exponential_error_absorbed
      (c := (1 : ℝ)) (by norm_num))
  filter_upwards [hrate, hsqrt, habsorb] with m hrate hsqrt habsorb
  have hrateExp : Real.exp (-sourceRate m) ≤
      Real.exp (-Real.log ((m : ℝ) + 1) ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [sourceRate, sourceRateExponent_eq]
    linarith
  have hsqrtExp : Real.exp (-Real.sqrt (m : ℝ)) ≤
      Real.exp (-Real.log ((m : ℝ) + 1) ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [Real.sqrt_eq_rpow]
    linarith
  have habsorb' : Real.exp (-Real.log ((m : ℝ) + 1) ^ 2) ≤
      ((m : ℝ) + 1) ^ (-(3 * kappa)) := by
    simpa only [Nat.cast_add, Nat.cast_one, neg_mul, one_mul,
      add_comm, mul_comm] using habsorb
  exact ⟨hrateExp.trans habsorb', hsqrtExp.trans habsorb'⟩

/-- Each of the two error scales occurring in Proposition 4.5 is eventually
below one copy of the exact source exceptional rate. -/
theorem eventually_source_errors_le_exceptional :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-sourceRate m)) ≤
          sourceExceptionalRate m kappa ∧
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) ≤
          sourceExceptionalRate m kappa := by
  filter_upwards [eventually_source_error_real_le_exceptional] with m hm
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  have hrateEq : ENNReal.ofReal (((m : ℝ) + 1) ^ (-(3 * kappa))) =
      sourceExceptionalRate m kappa := by
    rw [← ENNReal.ofReal_rpow_of_pos (by positivity), hbase]
    simp only [sourceExceptionalRate]
  constructor
  · exact (ENNReal.ofReal_le_ofReal hm.1).trans_eq hrateEq
  · exact (ENNReal.ofReal_le_ofReal hm.2).trans_eq hrateEq

/-- The complete four-branch error from the checked Proposition-4.5 core
is eventually absorbed with the explicit prefactor six. -/
theorem eventually_sourceProp45FourBranchError_le :
    ∀ᶠ m : ℕ in atTop,
      sourceProp45FourBranchError m ≤
        sourceExceptionalRateWithPrefactor m 6 kappa := by
  filter_upwards [eventually_source_errors_le_exceptional] with m hm
  rw [sourceProp45FourBranchError]
  have hpair :
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) ≤
        sourceExceptionalRate m kappa + sourceExceptionalRate m kappa :=
    add_le_add hm.1 hm.2
  have hthree :
      (ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
          ENNReal.ofReal (Real.exp (-sourceRate m)) ≤
        (sourceExceptionalRate m kappa + sourceExceptionalRate m kappa) +
          sourceExceptionalRate m kappa :=
    add_le_add hpair hm.1
  have hfive :
      ((ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
          ENNReal.ofReal (Real.exp (-sourceRate m))) +
          (ENNReal.ofReal (Real.exp (-sourceRate m)) +
            ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) ≤
        ((sourceExceptionalRate m kappa + sourceExceptionalRate m kappa) +
          sourceExceptionalRate m kappa) +
          (sourceExceptionalRate m kappa + sourceExceptionalRate m kappa) :=
    add_le_add hthree hpair
  calc
    (ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
        ENNReal.ofReal (Real.exp (-sourceRate m)) +
        (ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
        ENNReal.ofReal (Real.exp (-sourceRate m)) ≤
      (sourceExceptionalRate m kappa + sourceExceptionalRate m kappa) +
        sourceExceptionalRate m kappa +
        (sourceExceptionalRate m kappa + sourceExceptionalRate m kappa) +
        sourceExceptionalRate m kappa := by
      exact add_le_add hfive hm.1
    _ = sourceExceptionalRateWithPrefactor m 6 kappa := by
      simp only [sourceExceptionalRateWithPrefactor, Nat.cast_ofNat]
      ring

end Erdos1166.HLOZProp45SourceAbsorption
