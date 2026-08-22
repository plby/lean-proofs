/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Central

/-!
# Stirling estimates for Erdős Problem 1165

This file isolates the deterministic analytic estimates used when lattice
walk probabilities are reduced to factorial and binomial expressions.  It
contains no probabilistic assumptions.
-/

open Filter Real
open scoped Topology Nat Asymptotics

namespace Erdos1165.StirlingLocalCLT

/-- The logarithm of the main term in Stirling's formula. -/
noncomputable def logFactorialMain (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log n - n + Real.log n / 2 + Real.log (2 * Real.pi) / 2

/-- The additive error after subtracting the logarithmic Stirling main term. -/
noncomputable def logFactorialRemainder (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - logFactorialMain n

lemma logFactorial_eq_main_add_remainder (n : ℕ) :
    Real.log (n.factorial : ℝ) = logFactorialMain n + logFactorialRemainder n := by
  simp [logFactorialRemainder]

lemma logFactorialRemainder_eq_log_stirlingSeq {n : ℕ} (hn : n ≠ 0) :
    logFactorialRemainder n =
      Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) := by
  rw [logFactorialRemainder, logFactorialMain, Stirling.log_stirlingSeq_formula]
  rw [Real.log_div (by positivity : (n : ℝ) ≠ 0) (by positivity : Real.exp 1 ≠ 0)]
  rw [Real.log_exp]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : Real.pi ≠ 0)]
  rw [Real.log_sqrt (by positivity : 0 ≤ Real.pi)]
  ring

lemma logFactorialRemainder_nonneg {n : ℕ} (hn : n ≠ 0) :
    0 ≤ logFactorialRemainder n := by
  unfold logFactorialRemainder logFactorialMain
  exact sub_nonneg.mpr (Stirling.le_log_factorial_stirling hn)

lemma stirlingSeq_le_one {n : ℕ} (hn : n ≠ 0) :
    Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact Stirling.stirlingSeq'_antitone (Nat.zero_le k)

lemma logFactorialRemainder_le_one {n : ℕ} (hn : n ≠ 0) :
    logFactorialRemainder n ≤ 1 := by
  rw [logFactorialRemainder_eq_log_stirlingSeq hn]
  have hlog : Real.log (Stirling.stirlingSeq n) ≤
      Real.log (Stirling.stirlingSeq 1) := by
    exact Real.log_le_log_iff (by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      exact Stirling.stirlingSeq'_pos k) (Stirling.stirlingSeq'_pos 0) |>.2
        (stirlingSeq_le_one hn)
  rw [Stirling.stirlingSeq_one, Real.log_div (by positivity) (by positivity),
    Real.log_exp, Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2)] at hlog
  have hpi : 0 ≤ Real.log (Real.sqrt Real.pi) := by
    exact Real.log_nonneg (Real.one_le_sqrt.mpr (by linarith [Real.two_le_pi]))
  have hlogTwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  linarith

private lemma log_stirlingSeq_sub_add_le (n m : ℕ) (hn : n ≠ 0) :
    Real.log (Stirling.stirlingSeq n) -
        Real.log (Stirling.stirlingSeq (n + m)) ≤
      (1 : ℝ) / (12 * n) - 1 / (12 * (n + m)) := by
  let f (j : ℕ) : ℝ := Real.log (Stirling.stirlingSeq (n + j))
  let g (j : ℕ) : ℝ := 1 / (12 * (n + j) : ℝ)
  have hstep (j : ℕ) (hj : j ∈ Finset.range m) : f j - f (j + 1) ≤ g j - g (j + 1) := by
    have hnj : (0 : ℝ) < n + j := by
      exact_mod_cast Nat.add_pos_left (Nat.pos_of_ne_zero hn) j
    have hraw := Stirling.log_stirlingSeq_sdiff_le (n + j)
    dsimp only [f, g]
    push_cast
    rw [show n + (j + 1) = n + j + 1 by omega]
    rw [← add_assoc (n : ℝ) (j : ℝ) 1]
    calc
      Real.log (Stirling.stirlingSeq (n + j)) -
          Real.log (Stirling.stirlingSeq (n + j + 1))
          ≤ 1 / (12 * (n + j) * (n + j + 1)) := by
            simpa only [Nat.cast_add, Nat.cast_ofNat] using hraw
      _ = 1 / (12 * (n + j)) - 1 / (12 * (n + j + 1)) := by
        field_simp
        ring
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_range_sub', Finset.sum_range_sub'] at hsum
  simpa only [f, g, Nat.add_zero, Nat.cast_add, Nat.cast_zero, add_zero] using hsum

/-- Robbins' quantitative logarithmic Stirling remainder.  Unlike the coarse
uniform bound below, this estimate records the optimal `O(1/n)` scale. -/
lemma logFactorialRemainder_le_inv_twelve_mul {n : ℕ} (hn : n ≠ 0) :
    logFactorialRemainder n ≤ (1 : ℝ) / (12 * n) := by
  rw [logFactorialRemainder_eq_log_stirlingSeq hn]
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (Stirling.stirlingSeq (n + m))) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    have hs := Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat n)
    exact ((Real.continuousAt_log (by positivity)).tendsto.comp hs).congr' <|
      Filter.Eventually.of_forall fun m ↦ by simp only [Function.comp_apply, add_comm]
  have hinv : Tendsto (fun m : ℕ ↦ (1 : ℝ) / (12 * (n + m))) atTop (𝓝 0) := by
    have hbase := (tendsto_const_div_atTop_nhds_zero_nat (1 / 12 : ℝ)).comp
      (tendsto_add_atTop_nat n)
    exact hbase.congr' <| Filter.Eventually.of_forall fun m ↦ by
      simp only [Function.comp_apply, Nat.cast_add, add_comm]
      have hnm : (0 : ℝ) < n + m := by
        exact_mod_cast Nat.add_pos_left (Nat.pos_of_ne_zero hn) m
      field_simp
  have hleft : Tendsto (fun m : ℕ ↦ Real.log (Stirling.stirlingSeq n) -
      Real.log (Stirling.stirlingSeq (n + m))) atTop
      (𝓝 (Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi))) :=
    tendsto_const_nhds.sub hlog
  have hright : Tendsto (fun m : ℕ ↦ (1 : ℝ) / (12 * n) -
      1 / (12 * (n + m))) atTop (𝓝 ((1 : ℝ) / (12 * n))) := by
    simpa using (tendsto_const_nhds.sub hinv)
  exact le_of_tendsto_of_tendsto hleft hright <|
    Filter.Eventually.of_forall fun m ↦ log_stirlingSeq_sub_add_le n m hn

lemma abs_logFactorialRemainder_le_one {n : ℕ} (hn : n ≠ 0) :
    |logFactorialRemainder n| ≤ 1 := by
  rw [abs_of_nonneg (logFactorialRemainder_nonneg hn)]
  exact logFactorialRemainder_le_one hn

/-- The logarithmic remainder in Stirling's formula tends to zero. -/
lemma tendsto_logFactorialRemainder_zero :
    Tendsto logFactorialRemainder atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (Stirling.stirlingSeq n)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have hsub := hlog.sub
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ Real.log (Real.sqrt Real.pi)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))))
  apply (show Tendsto (fun n : ℕ ↦ Real.log (Stirling.stirlingSeq n) -
      Real.log (Real.sqrt Real.pi)) atTop (𝓝 0) by simpa using hsub).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (logFactorialRemainder_eq_log_stirlingSeq (Nat.ne_of_gt hn)).symm

/-- Global elementary upper bound for the central binomial coefficient. -/
lemma centralBinom_le_four_pow (n : ℕ) :
    (Nat.centralBinom n : ℝ) ≤ (4 : ℝ) ^ n := by
  exact_mod_cast Nat.centralBinom_le_four_pow n

/-- Global elementary lower bound for the central binomial coefficient.  This
version avoids square roots and is often convenient before Stirling estimates
are introduced. -/
lemma four_pow_le_two_mul_mul_centralBinom {n : ℕ} (hn : n ≠ 0) :
    (4 : ℝ) ^ n ≤ 2 * n * (Nat.centralBinom n : ℝ) := by
  exact_mod_cast Nat.four_pow_le_two_mul_self_mul_centralBinom n (Nat.pos_of_ne_zero hn)

/-- The central binomial probability is trapped between `1/(2n)` and `1`. -/
lemma centralBinom_div_four_pow_bounds {n : ℕ} (hn : n ≠ 0) :
    (1 : ℝ) / (2 * n) ≤ (Nat.centralBinom n : ℝ) / 4 ^ n ∧
      (Nat.centralBinom n : ℝ) / 4 ^ n ≤ 1 := by
  constructor
  · rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n) (by positivity : (0 : ℝ) < 4 ^ n)]
    nlinarith [four_pow_le_two_mul_mul_centralBinom hn]
  · rw [div_le_one (by positivity : (0 : ℝ) < 4 ^ n)]
    exact centralBinom_le_four_pow n

/-! ## Uniform logarithmic errors for binomial coefficients -/

/-- The entropy-scale main term for a binomial coefficient, expressed in a
form that is robust at the level of factorial identities. -/
noncomputable def logBinomialMain (n k : ℕ) : ℝ :=
  logFactorialMain n - logFactorialMain k - logFactorialMain (n - k)

/-- The error after subtracting the three Stirling main terms from a binomial
coefficient. -/
noncomputable def logBinomialRemainder (n k : ℕ) : ℝ :=
  Real.log (n.choose k : ℝ) - logBinomialMain n k

lemma log_choose_eq_log_factorials {n k : ℕ} (hk : k ≤ n) :
    Real.log (n.choose k : ℝ) = Real.log (n.factorial : ℝ) -
      Real.log (k.factorial : ℝ) - Real.log ((n - k).factorial : ℝ) := by
  have hfac : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) =
      (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hchoose : (n.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hnkfac : ((n - k).factorial : ℝ) ≠ 0 := by positivity
  have hlog := congrArg Real.log hfac
  rw [Real.log_mul (mul_ne_zero hchoose hkfac) hnkfac,
    Real.log_mul hchoose hkfac] at hlog
  linarith

lemma logBinomialRemainder_eq {n k : ℕ} (hk : k ≤ n) :
    logBinomialRemainder n k = logFactorialRemainder n -
      logFactorialRemainder k - logFactorialRemainder (n - k) := by
  rw [logBinomialRemainder, logBinomialMain, log_choose_eq_log_factorials hk]
  simp only [logFactorialRemainder, logFactorialMain]
  ring

/-- A uniform error bound for Stirling's approximation to every interior
binomial coefficient.  The constant `2` is deliberately coarse but independent
of both parameters, which is the feature needed in local-limit estimates. -/
lemma abs_logBinomialRemainder_le_two {n k : ℕ} (hk0 : k ≠ 0) (hkn : k < n) :
    |logBinomialRemainder n k| ≤ 2 := by
  rw [logBinomialRemainder_eq hkn.le]
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hkn)
  have hnk0 : n - k ≠ 0 := (Nat.sub_pos_iff_lt.mpr hkn).ne'
  have hn_lo := logFactorialRemainder_nonneg hn0
  have hk_lo := logFactorialRemainder_nonneg hk0
  have hnk_lo := logFactorialRemainder_nonneg hnk0
  have hn_hi := logFactorialRemainder_le_one hn0
  have hk_hi := logFactorialRemainder_le_one hk0
  have hnk_hi := logFactorialRemainder_le_one hnk0
  rw [abs_le]
  constructor <;> linarith

/-- Robbins' bounds give a parameter-dependent version of the uniform
binomial remainder estimate.  In particular, this error tends uniformly to
zero whenever all three factorial arguments tend to infinity. -/
lemma logBinomialRemainder_robbins_bounds {n k : ℕ} (hk0 : k ≠ 0) (hkn : k < n) :
    -((1 : ℝ) / (12 * k) + 1 / (12 * (n - k))) ≤ logBinomialRemainder n k ∧
      logBinomialRemainder n k ≤ (1 : ℝ) / (12 * n) := by
  rw [logBinomialRemainder_eq hkn.le]
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hkn)
  have hnk0 : n - k ≠ 0 := (Nat.sub_pos_iff_lt.mpr hkn).ne'
  have hn_hi := logFactorialRemainder_le_inv_twelve_mul hn0
  have hk_hi := logFactorialRemainder_le_inv_twelve_mul hk0
  have hnk_hi := logFactorialRemainder_le_inv_twelve_mul hnk0
  rw [Nat.cast_sub hkn.le] at hnk_hi
  constructor
  · linarith [logFactorialRemainder_nonneg hn0,
      hk_hi, hnk_hi]
  · linarith [hn_hi,
      logFactorialRemainder_nonneg hk0, logFactorialRemainder_nonneg hnk0]

/-- Filter-level (hence triangular-array) form of the binomial Stirling
estimate. -/
lemma tendsto_logBinomialRemainder_zero
    {α : Type*} {l : Filter α} {n k : α → ℕ}
    (hn : Tendsto n l atTop) (hk : Tendsto k l atTop)
    (hnk : Tendsto (fun i ↦ n i - k i) l atTop)
    (hkn : ∀ᶠ i in l, k i ≤ n i) :
    Tendsto (fun i ↦ logBinomialRemainder (n i) (k i)) l (𝓝 0) := by
  have hnrem := tendsto_logFactorialRemainder_zero.comp hn
  have hkrem := tendsto_logFactorialRemainder_zero.comp hk
  have hnkrem := tendsto_logFactorialRemainder_zero.comp hnk
  have hdiff := (hnrem.sub hkrem).sub hnkrem
  apply (show Tendsto (fun i ↦ logFactorialRemainder (n i) -
      logFactorialRemainder (k i) - logFactorialRemainder (n i - k i)) l (𝓝 0) by
        simpa using hdiff).congr'
  filter_upwards [hkn] with i hi
  exact (logBinomialRemainder_eq hi).symm

/-! ## Central binomial coefficients at the local-CLT scale -/

/-- The logarithmic error in the standard central-binomial approximation
`choose (2n) n ≈ 4^n / sqrt (π n)`. -/
noncomputable def centralBinomialLogError (n : ℕ) : ℝ :=
  Real.log (Nat.centralBinom n : ℝ) -
    ((n : ℝ) * Real.log 4 - Real.log (Real.pi * n) / 2)

lemma central_main_term {n : ℕ} (hn : n ≠ 0) :
    logFactorialMain (2 * n) - 2 * logFactorialMain n =
      (n : ℝ) * Real.log 4 - Real.log (Real.pi * n) / 2 := by
  simp only [logFactorialMain, Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
  rw [show (4 : ℝ) = 2 * 2 by norm_num,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.log_mul (by positivity : Real.pi ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : Real.pi ≠ 0)]
  ring

lemma centralBinomialLogError_eq {n : ℕ} (hn : n ≠ 0) :
    centralBinomialLogError n =
      logFactorialRemainder (2 * n) - 2 * logFactorialRemainder n := by
  have hchoose := logBinomialRemainder_eq (n := 2 * n) (k := n)
    (Nat.le_mul_of_pos_left n zero_lt_two)
  have hsub : 2 * n - n = n := by omega
  rw [logBinomialRemainder, logBinomialMain, hsub] at hchoose
  change Real.log (Nat.centralBinom n : ℝ) -
      (logFactorialMain (2 * n) - logFactorialMain n - logFactorialMain n) =
    logFactorialRemainder (2 * n) - logFactorialRemainder n -
      logFactorialRemainder n at hchoose
  rw [centralBinomialLogError, ← central_main_term hn]
  linarith

lemma centralBinomialLogError_bounds {n : ℕ} (hn : n ≠ 0) :
    -2 ≤ centralBinomialLogError n ∧ centralBinomialLogError n ≤ 1 := by
  rw [centralBinomialLogError_eq hn]
  have h2n : 2 * n ≠ 0 := mul_ne_zero (by norm_num) hn
  constructor
  · linarith [logFactorialRemainder_nonneg h2n,
      logFactorialRemainder_le_one hn]
  · linarith [logFactorialRemainder_le_one h2n,
      logFactorialRemainder_nonneg hn]

/-- Sharp `O(1/n)` two-sided control of the central-binomial logarithmic
error, directly inherited from Robbins' factorial remainder bound. -/
lemma centralBinomialLogError_robbins_bounds {n : ℕ} (hn : n ≠ 0) :
    -2 * ((1 : ℝ) / (12 * n)) ≤ centralBinomialLogError n ∧
      centralBinomialLogError n ≤ (1 : ℝ) / (12 * (2 * n)) := by
  rw [centralBinomialLogError_eq hn]
  have h2n : 2 * n ≠ 0 := mul_ne_zero (by norm_num) hn
  have hn_hi := logFactorialRemainder_le_inv_twelve_mul hn
  have h2n_hi := logFactorialRemainder_le_inv_twelve_mul h2n
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h2n_hi
  constructor
  · linarith [logFactorialRemainder_nonneg h2n,
      hn_hi]
  · linarith [h2n_hi,
      logFactorialRemainder_nonneg hn]

lemma abs_centralBinomialLogError_le_two {n : ℕ} (hn : n ≠ 0) :
    |centralBinomialLogError n| ≤ 2 := by
  rw [abs_le]
  have h := centralBinomialLogError_bounds hn
  constructor
  · exact h.1
  · linarith [h.2]

lemma tendsto_centralBinomialLogError_zero :
    Tendsto centralBinomialLogError atTop (𝓝 0) := by
  have htwo : Tendsto (fun n : ℕ ↦ logFactorialRemainder (2 * n)) atTop (𝓝 0) :=
    tendsto_logFactorialRemainder_zero.comp
      (tendsto_id.const_mul_atTop' (by norm_num : 0 < (2 : ℕ)))
  have hdiff := htwo.sub (tendsto_logFactorialRemainder_zero.const_mul 2)
  apply (show Tendsto (fun n : ℕ ↦ logFactorialRemainder (2 * n) -
      2 * logFactorialRemainder n) atTop (𝓝 0) by simpa using hdiff).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (centralBinomialLogError_eq (Nat.ne_of_gt hn)).symm

/-- Exponentiating the logarithmic error gives exactly the usual normalized
central binomial coefficient. -/
lemma centralBinom_normalized_eq_exp_error {n : ℕ} (hn : n ≠ 0) :
    (Nat.centralBinom n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n =
      Real.exp (centralBinomialLogError n) := by
  have hcentral : (0 : ℝ) < Nat.centralBinom n := by
    exact_mod_cast Nat.centralBinom_pos n
  have hsqrt : Real.exp (Real.log (Real.pi * n) / 2) =
      Real.sqrt (Real.pi * n) := by
    rw [← Real.log_sqrt (by positivity : (0 : ℝ) ≤ Real.pi * n)]
    exact Real.exp_log (by positivity)
  have hpow : Real.exp ((n : ℝ) * Real.log 4) = (4 : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [centralBinomialLogError, Real.exp_sub, Real.exp_sub,
    Real.exp_log hcentral, hpow, hsqrt]
  field_simp

/-- Explicit square-root-scale bounds for the central binomial coefficient. -/
lemma centralBinom_normalized_bounds {n : ℕ} (hn : n ≠ 0) :
    Real.exp (-2) ≤
        (Nat.centralBinom n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n ∧
      (Nat.centralBinom n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n ≤
        Real.exp 1 := by
  rw [centralBinom_normalized_eq_exp_error hn]
  have h := centralBinomialLogError_bounds hn
  exact ⟨Real.exp_le_exp.mpr h.1, Real.exp_le_exp.mpr h.2⟩

/-- Robbins' sharper `1/n` version of the normalized central-binomial bounds. -/
lemma centralBinom_normalized_robbins_bounds {n : ℕ} (hn : n ≠ 0) :
    Real.exp (-2 * ((1 : ℝ) / (12 * n))) ≤
        (Nat.centralBinom n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n ∧
      (Nat.centralBinom n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n ≤
        Real.exp ((1 : ℝ) / (12 * (2 * n))) := by
  rw [centralBinom_normalized_eq_exp_error hn]
  have h := centralBinomialLogError_robbins_bounds hn
  exact ⟨Real.exp_le_exp.mpr h.1, Real.exp_le_exp.mpr h.2⟩

/-- The central binomial local limit theorem in its standard normalized form. -/
theorem tendsto_centralBinom_normalized_one :
    Tendsto (fun n : ℕ ↦
      (Nat.centralBinom n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)
      atTop (𝓝 1) := by
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp (centralBinomialLogError n))
      atTop (𝓝 1) := by
    exact Real.tendsto_exp_nhds_zero_nhds_one.comp tendsto_centralBinomialLogError_zero
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (centralBinom_normalized_eq_exp_error (Nat.ne_of_gt hn)).symm

end Erdos1165.StirlingLocalCLT
