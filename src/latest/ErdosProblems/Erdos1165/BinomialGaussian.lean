/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.StirlingLocalCLT

/-!
# Uniform Gaussian estimates for the symmetric binomial law

This file derives finite local-CLT estimates for the point masses of a
`Binomial(N, 1/2)` variable.  There is no asymptotic or probabilistic assumption in
the development: the estimates follow from the Robbins bounds in
`StirlingLocalCLT.lean` and an explicit Taylor estimate for `log (1 + u)`.

We state the main results for an even number `2 * n` of trials and the upper
point `n + d`.  The lower point `n - d` has exactly the same mass.  On the
moderate window `2 * d ≤ n`, the logarithm of the normalized mass differs
from its Gaussian approximation by at most

`8 n (d/n)^3 + (d/n)^2 + 1/(6(n-d))`.

In particular, the error tends to zero uniformly in every family satisfying
`d^3/n^2 -> 0` (and hence in the usual `d = O(sqrt(n log n))` window).
-/

open Filter Real
open scoped Nat Topology

namespace Erdos1165.BinomialGaussian

open StirlingLocalCLT

/-- The point mass `P(Binomial(N,1/2)=k)`. -/
noncomputable def symBinomialMass (N k : ℕ) : ℝ :=
  (N.choose k : ℝ) / (2 : ℝ) ^ N

/-- The point mass at the upper centered point `n+d` among `2n` trials. -/
noncomputable def evenSymmetricMass (n d : ℕ) : ℝ :=
  symBinomialMass (2 * n) (n + d)

/-- The displacement from the center, divided by the half-length. -/
noncomputable def relativeDeviation (n d : ℕ) : ℝ := (d : ℝ) / n

/-- The symmetric entropy function controlling centered binomial masses. -/
noncomputable def symmetricEntropy (u : ℝ) : ℝ :=
  (1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u)

/-- The logarithmic error after dividing out the Gaussian local-CLT term. -/
noncomputable def evenGaussianLogError (n d : ℕ) : ℝ :=
  Real.log (evenSymmetricMass n d) + Real.log (Real.pi * n) / 2 +
    (d : ℝ) ^ 2 / n

lemma symBinomialMass_pos {N k : ℕ} (hk : k ≤ N) :
    0 < symBinomialMass N k := by
  unfold symBinomialMass
  have hchoose : (0 : ℝ) < N.choose k := by
    exact_mod_cast Nat.choose_pos hk
  exact div_pos hchoose (by positivity)

lemma evenSymmetricMass_pos {n d : ℕ} (hd : d ≤ n) :
    0 < evenSymmetricMass n d := by
  apply symBinomialMass_pos
  omega

/-- Exact symmetry between the upper and lower centered point masses. -/
lemma evenSymmetricMass_sub_eq_add {n d : ℕ} (hd : d ≤ n) :
    symBinomialMass (2 * n) (n - d) = evenSymmetricMass n d := by
  unfold evenSymmetricMass symBinomialMass
  have hle : n - d ≤ 2 * n := by omega
  rw [← Nat.choose_symm hle]
  congr 3
  omega

private lemma abs_log_one_add_sub_linear_add_quadratic_le
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - u + u ^ 2 / 2| ≤ 2 * |u| ^ 3 := by
  have hu' : |-u| < 1 := by simpa using hu.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  have h := Real.abs_log_sub_add_sum_range_le hu' 2
  norm_num [Finset.sum_range_succ, pow_two] at h
  have hden : 0 < 1 - |u| := sub_pos.mpr (hu.trans_lt (by norm_num))
  have hinv : (1 - |u|)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h' : |Real.log (1 + u) - u + u ^ 2 / 2| ≤ |u| ^ 3 / (1 - |u|) := by
    convert h using 1
    all_goals ring_nf
  calc
    |Real.log (1 + u) - u + u ^ 2 / 2| ≤ |u| ^ 3 / (1 - |u|) := h'
    _ = |u| ^ 3 * (1 - |u|)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ |u| ^ 3 * 2 := mul_le_mul_of_nonneg_left hinv (pow_nonneg (abs_nonneg u) 3)
    _ = 2 * |u| ^ 3 := by ring

private lemma abs_entropyRemainder_le
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |(1 + u) * Real.log (1 + u) - u - u ^ 2 / 2| ≤ 4 * |u| ^ 3 := by
  have hlog := abs_log_one_add_sub_linear_add_quadratic_le hu
  have hu1 : |1 + u| ≤ 3 / 2 := by
    calc
      |1 + u| ≤ 1 + |u| := by simpa using abs_add_le 1 u
      _ ≤ 3 / 2 := by linarith
  have hid : (1 + u) * Real.log (1 + u) - u - u ^ 2 / 2 =
      (1 + u) * (Real.log (1 + u) - u + u ^ 2 / 2) - u ^ 3 / 2 := by ring
  rw [hid]
  calc
    |(1 + u) * (Real.log (1 + u) - u + u ^ 2 / 2) - u ^ 3 / 2| ≤
        |1 + u| * |Real.log (1 + u) - u + u ^ 2 / 2| + |u ^ 3 / 2| :=
      (abs_sub _ _).trans_eq (by rw [abs_mul])
    _ ≤ (3 / 2) * (2 * |u| ^ 3) + |u| ^ 3 / 2 := by
      rw [abs_div, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
    _ ≤ 4 * |u| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg u) 3]

/-- Cubic, fully explicit control of the symmetric entropy remainder. -/
lemma abs_symmetricEntropy_sub_sq_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |symmetricEntropy u - u ^ 2| ≤ 8 * |u| ^ 3 := by
  have hp := abs_entropyRemainder_le hu
  have hm := abs_entropyRemainder_le (u := -u) (by simpa using hu)
  unfold symmetricEntropy
  have hid :
      (1 + u) * Real.log (1 + u) + (1 - u) * Real.log (1 - u) - u ^ 2 =
        ((1 + u) * Real.log (1 + u) - u - u ^ 2 / 2) +
        ((1 + (-u)) * Real.log (1 + (-u)) - (-u) - (-u) ^ 2 / 2) := by ring_nf
  rw [hid]
  calc
    |((1 + u) * Real.log (1 + u) - u - u ^ 2 / 2) +
        ((1 + -u) * Real.log (1 + -u) - -u - (-u) ^ 2 / 2)| ≤
        |(1 + u) * Real.log (1 + u) - u - u ^ 2 / 2| +
          |(1 + -u) * Real.log (1 + -u) - -u - (-u) ^ 2 / 2| := abs_add_le _ _
    _ ≤ 4 * |u| ^ 3 + 4 * |-u| ^ 3 := add_le_add hp hm
    _ = 8 * |u| ^ 3 := by rw [abs_neg]; ring

private lemma abs_log_one_add_le_two_mul_abs
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u)| ≤ 2 * |u| := by
  have hrem := abs_log_one_add_sub_linear_add_quadratic_le hu
  have hz : 0 ≤ |u| := abs_nonneg u
  have hid : Real.log (1 + u) =
      (Real.log (1 + u) - u + u ^ 2 / 2) + u - u ^ 2 / 2 := by ring
  rw [hid]
  calc
    |(Real.log (1 + u) - u + u ^ 2 / 2) + u - u ^ 2 / 2| ≤
        |Real.log (1 + u) - u + u ^ 2 / 2| + |u| + |u ^ 2 / 2| := by
      calc
        _ ≤ |(Real.log (1 + u) - u + u ^ 2 / 2) + u| + |u ^ 2 / 2| :=
          abs_sub _ _
        _ ≤ (|Real.log (1 + u) - u + u ^ 2 / 2| + |u|) + |u ^ 2 / 2| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ 2 * |u| ^ 3 + |u| + |u| ^ 2 / 2 := by
      rw [abs_div, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      gcongr
    _ ≤ 2 * |u| := by nlinarith [sq_nonneg (|u| - 1 / 2)]

private lemma abs_log_one_sub_sq_half_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 - u ^ 2) / 2| ≤ u ^ 2 := by
  have hu_sq : 0 ≤ u ^ 2 := sq_nonneg u
  have hu_sq_le : u ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]
    have h := (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hu
    norm_num at h ⊢
    exact h
  have hsmall : |-u ^ 2| ≤ 1 / 2 := by
    rw [abs_neg, abs_of_nonneg hu_sq]
    linarith
  have hlog := abs_log_one_add_le_two_mul_abs hsmall
  rw [show 1 + -u ^ 2 = 1 - u ^ 2 by ring, abs_neg, abs_of_nonneg hu_sq] at hlog
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

private lemma log_evenSymmetricMass_eq_main_add_remainder
    {n d : ℕ} (_hn : 0 < n) (hd : d < n) :
    Real.log (evenSymmetricMass n d) =
      logBinomialMain (2 * n) (n + d) - (2 * n : ℕ) * Real.log 2 +
        logBinomialRemainder (2 * n) (n + d) := by
  have hle : n + d ≤ 2 * n := by omega
  have hchoose : (0 : ℝ) < (2 * n).choose (n + d) := by
    exact_mod_cast Nat.choose_pos hle
  unfold evenSymmetricMass symBinomialMass
  rw [Real.log_div (ne_of_gt hchoose) (by positivity : (2 : ℝ) ^ (2 * n) ≠ 0),
    Real.log_pow]
  rw [show Real.log (((2 * n).choose (n + d) : ℕ) : ℝ) =
      logBinomialMain (2 * n) (n + d) +
        logBinomialRemainder (2 * n) (n + d) by
    simp only [logBinomialRemainder]
    ring]
  push_cast
  ring

private lemma logBinomialMain_centered_eq
    {n d : ℕ} (hn : 0 < n) (hd : d < n) :
    logBinomialMain (2 * n) (n + d) - (2 * n : ℕ) * Real.log 2 =
      -((n : ℝ) * symmetricEntropy (relativeDeviation n d)) -
        Real.log (Real.pi * n) / 2 -
        Real.log (1 - relativeDeviation n d ^ 2) / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hplus : (n + d : ℝ) = (n : ℝ) * (1 + relativeDeviation n d) := by
    unfold relativeDeviation
    field_simp
  have hminus : (n - d : ℝ) = (n : ℝ) * (1 - relativeDeviation n d) := by
    unfold relativeDeviation
    field_simp
  have hrel_lt : relativeDeviation n d < 1 := by
    unfold relativeDeviation
    exact (div_lt_one (by positivity : (0 : ℝ) < n)).2 (by exact_mod_cast hd)
  have hrel_nonneg : 0 ≤ relativeDeviation n d := by
    unfold relativeDeviation
    positivity
  have hp : 0 < 1 + relativeDeviation n d := by linarith
  have hm : 0 < 1 - relativeDeviation n d := sub_pos.mpr hrel_lt
  have hprod : 1 - relativeDeviation n d ^ 2 =
      (1 + relativeDeviation n d) * (1 - relativeDeviation n d) := by ring
  unfold logBinomialMain logFactorialMain
  rw [show 2 * n - (n + d) = n - d by omega]
  push_cast [hd.le]
  rw [hplus, hminus,
    Real.log_mul hn0 hp.ne', Real.log_mul hn0 hm.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0,
    Real.log_mul (by positivity : Real.pi ≠ 0) hn0,
    hprod, Real.log_mul hp.ne' hm.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : Real.pi ≠ 0)]
  unfold relativeDeviation symmetricEntropy
  field_simp
  ring

/-- Exact decomposition of the centered log mass into its Gaussian term,
the entropy remainder, the square-root prefactor correction, and Robbins'
factorial remainder. -/
lemma evenGaussianLogError_eq {n d : ℕ} (hn : 0 < n) (hd : d < n) :
    evenGaussianLogError n d =
      -((n : ℝ) *
          (symmetricEntropy (relativeDeviation n d) - relativeDeviation n d ^ 2)) -
        Real.log (1 - relativeDeviation n d ^ 2) / 2 +
        logBinomialRemainder (2 * n) (n + d) := by
  rw [evenGaussianLogError, log_evenSymmetricMass_eq_main_add_remainder hn hd,
    logBinomialMain_centered_eq hn hd]
  unfold relativeDeviation
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private lemma abs_logBinomialRemainder_centered_le
    {n d : ℕ} (hn : 0 < n) (hd : d < n) :
    |logBinomialRemainder (2 * n) (n + d)| ≤ (1 : ℝ) / (6 * (n - d)) := by
  have hk0 : n + d ≠ 0 := by omega
  have hkn : n + d < 2 * n := by omega
  have hbounds := logBinomialRemainder_robbins_bounds hk0 hkn
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hbounds
  have hsub : (2 : ℝ) * n - (n + d) = ((n - d : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd.le]
    ring
  rw [hsub] at hbounds
  rw [Nat.cast_sub hd.le] at hbounds
  have hminus_pos : (0 : ℝ) < n - d := by
    exact sub_pos.mpr (by exact_mod_cast hd)
  have hplus_ge : (n - d : ℝ) ≤ n + d := by
    nlinarith [show (0 : ℝ) ≤ d by positivity]
  have hplus_pos : (0 : ℝ) < n + d := by positivity
  have hinv_plus : (1 : ℝ) / (12 * (n + d)) ≤ 1 / (12 * (n - d)) := by
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hupper : (1 : ℝ) / (12 * (2 * n)) ≤ 1 / (6 * (n - d)) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 12 * (2 * n))
      (by positivity : (0 : ℝ) < 6 * (n - d))]
    nlinarith [show (d : ℝ) ≥ 0 by positivity]
  rw [abs_le]
  constructor
  · calc
      -((1 : ℝ) / (6 * (n - d))) ≤
          -((1 : ℝ) / (12 * (n + d)) + 1 / (12 * (n - d))) := by
        rw [neg_le_neg_iff]
        calc
          (1 : ℝ) / (12 * (n + d)) + 1 / (12 * (n - d)) ≤
              1 / (12 * (n - d)) + 1 / (12 * (n - d)) :=
            add_le_add hinv_plus le_rfl
          _ = 1 / (6 * (n - d)) := by
            field_simp
            ring
      _ ≤ logBinomialRemainder (2 * n) (n + d) := hbounds.1
  · exact hbounds.2.trans hupper

/-- **Uniform finite Gaussian local estimate.**  In the moderate window
`2d ≤ n`, the explicit logarithmic error is cubic in the relative deviation,
apart from the quadratic prefactor correction and the Robbins `O(1/n)` term. -/
theorem abs_evenGaussianLogError_le {n d : ℕ}
    (hn : 0 < n) (hd : d < n) (hmoderate : 2 * d ≤ n) :
    |evenGaussianLogError n d| ≤
      8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
        (1 : ℝ) / (6 * (n - d)) := by
  have hu_nonneg : 0 ≤ relativeDeviation n d := by
    unfold relativeDeviation
    positivity
  have hu : |relativeDeviation n d| ≤ 1 / 2 := by
    rw [abs_of_nonneg hu_nonneg]
    unfold relativeDeviation
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n)]
    have hm : (2 : ℝ) * d ≤ n := by exact_mod_cast hmoderate
    nlinarith
  have hent := abs_symmetricEntropy_sub_sq_le hu
  have hlog := abs_log_one_sub_sq_half_le hu
  have hrem := abs_logBinomialRemainder_centered_le hn hd
  rw [evenGaussianLogError_eq hn hd]
  calc
    |-((n : ℝ) *
          (symmetricEntropy (relativeDeviation n d) - relativeDeviation n d ^ 2)) -
        Real.log (1 - relativeDeviation n d ^ 2) / 2 +
        logBinomialRemainder (2 * n) (n + d)| ≤
        (n : ℝ) * |symmetricEntropy (relativeDeviation n d) -
          relativeDeviation n d ^ 2| +
          |Real.log (1 - relativeDeviation n d ^ 2) / 2| +
          |logBinomialRemainder (2 * n) (n + d)| := by
      calc
        _ ≤ |-((n : ℝ) *
              (symmetricEntropy (relativeDeviation n d) - relativeDeviation n d ^ 2)) -
              Real.log (1 - relativeDeviation n d ^ 2) / 2| +
              |logBinomialRemainder (2 * n) (n + d)| := abs_add_le _ _
        _ ≤ (|(n : ℝ) *
              (symmetricEntropy (relativeDeviation n d) - relativeDeviation n d ^ 2)| +
              |Real.log (1 - relativeDeviation n d ^ 2) / 2|) +
              |logBinomialRemainder (2 * n) (n + d)| := by
            gcongr
            simpa only [abs_neg] using
              (abs_sub (-((n : ℝ) *
                (symmetricEntropy (relativeDeviation n d) - relativeDeviation n d ^ 2)))
                (Real.log (1 - relativeDeviation n d ^ 2) / 2))
        _ = _ := by rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
    _ ≤ (n : ℝ) * (8 * |relativeDeviation n d| ^ 3) +
          relativeDeviation n d ^ 2 + (1 : ℝ) / (6 * (n - d)) := by
      gcongr
    _ = 8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
          (1 : ℝ) / (6 * (n - d)) := by ring

/-- Exponentiated two-sided local-CLT bound.  The middle expression is
exactly the point mass divided by the Gaussian approximation
`exp(-d^2/n) / sqrt(πn)`. -/
theorem evenSymmetricMass_gaussian_bounds {n d : ℕ}
    (hn : 0 < n) (hd : d < n) (hmoderate : 2 * d ≤ n) :
    let E := 8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
      (1 : ℝ) / (6 * (n - d))
    Real.exp (-E) ≤ evenSymmetricMass n d * Real.sqrt (Real.pi * n) *
        Real.exp ((d : ℝ) ^ 2 / n) ∧
      evenSymmetricMass n d * Real.sqrt (Real.pi * n) *
        Real.exp ((d : ℝ) ^ 2 / n) ≤ Real.exp E := by
  dsimp only
  have herr := abs_evenGaussianLogError_le hn hd hmoderate
  rw [abs_le] at herr
  have hmass := evenSymmetricMass_pos hd.le
  have hsqrt : Real.exp (Real.log (Real.pi * n) / 2) =
      Real.sqrt (Real.pi * n) := by
    rw [← Real.log_sqrt (by positivity : (0 : ℝ) ≤ Real.pi * n)]
    exact Real.exp_log (by positivity)
  have hnorm : Real.exp (evenGaussianLogError n d) =
      evenSymmetricMass n d * Real.sqrt (Real.pi * n) *
        Real.exp ((d : ℝ) ^ 2 / n) := by
    unfold evenGaussianLogError
    rw [Real.exp_add, Real.exp_add, Real.exp_log hmass, hsqrt]
  rw [← hnorm]
  exact ⟨Real.exp_le_exp.mpr herr.1, Real.exp_le_exp.mpr herr.2⟩

/-- The same Gaussian estimate at the lower centered point `n-d`. -/
theorem evenSymmetricMass_lower_gaussian_bounds {n d : ℕ}
    (hn : 0 < n) (hd : d < n) (hmoderate : 2 * d ≤ n) :
    let E := 8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
      (1 : ℝ) / (6 * (n - d))
    Real.exp (-E) ≤ symBinomialMass (2 * n) (n - d) * Real.sqrt (Real.pi * n) *
        Real.exp ((d : ℝ) ^ 2 / n) ∧
      symBinomialMass (2 * n) (n - d) * Real.sqrt (Real.pi * n) *
        Real.exp ((d : ℝ) ^ 2 / n) ≤ Real.exp E := by
  rw [evenSymmetricMass_sub_eq_add hd.le]
  exact evenSymmetricMass_gaussian_bounds hn hd hmoderate

/-- Ratio form of the moderate-deviation estimate, normalized by the central
point mass.  This avoids the square-root prefactor and is convenient for
screening arguments. -/
theorem evenSymmetricMass_ratio_gaussian_bounds {n d : ℕ}
    (hn : 0 < n) (hd : d < n) (hmoderate : 2 * d ≤ n) :
    let E := 8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
      (1 : ℝ) / (6 * (n - d)) + (1 : ℝ) / (6 * n)
    Real.exp (-E) ≤
        evenSymmetricMass n d / evenSymmetricMass n 0 *
          Real.exp ((d : ℝ) ^ 2 / n) ∧
      evenSymmetricMass n d / evenSymmetricMass n 0 *
          Real.exp ((d : ℝ) ^ 2 / n) ≤ Real.exp E := by
  dsimp only
  have hd0 : 0 < n := hn
  have hmod0 : 2 * 0 ≤ n := by omega
  have he := abs_evenGaussianLogError_le hn hd hmoderate
  have he0 := abs_evenGaussianLogError_le hn hd0 hmod0
  simp only [relativeDeviation, Nat.cast_zero, zero_div, abs_zero, zero_pow (by norm_num : 3 ≠ 0),
    mul_zero, zero_add, zero_pow (by norm_num : 2 ≠ 0)] at he0
  have he0' : |evenGaussianLogError n 0| ≤ (1 : ℝ) / (6 * n) := by
    simpa using he0
  have hdiff : |evenGaussianLogError n d - evenGaussianLogError n 0| ≤
      (8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
        (1 : ℝ) / (6 * (n - d))) + (1 : ℝ) / (6 * n) := by
    exact (abs_sub _ _).trans (add_le_add he he0')
  rw [abs_le] at hdiff
  have hmass := evenSymmetricMass_pos hd.le
  have hcenter := evenSymmetricMass_pos (n := n) (d := 0) (by omega)
  have hnorm : Real.exp (evenGaussianLogError n d - evenGaussianLogError n 0) =
      evenSymmetricMass n d / evenSymmetricMass n 0 *
        Real.exp ((d : ℝ) ^ 2 / n) := by
    unfold evenGaussianLogError
    rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
      Real.exp_log hmass, Real.exp_log hcenter]
    norm_num only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, Real.exp_zero,
      mul_one]
    field_simp
  rw [← hnorm]
  exact ⟨Real.exp_le_exp.mpr hdiff.1, Real.exp_le_exp.mpr hdiff.2⟩

/-- The central point mass is maximal.  This global fact has no moderate-range
hypothesis and is also valid when `n+d` lies outside the support. -/
theorem evenSymmetricMass_le_center (n d : ℕ) :
    evenSymmetricMass n d ≤ evenSymmetricMass n 0 := by
  unfold evenSymmetricMass symBinomialMass
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.choose_le_centralBinom (n + d) n
  · positivity

/-- Quantitative ratio-loss form.  For fixed `d` the coefficient on the
right is `O((d^2+1)/n)`; this form is useful when summing differences of
nearby centered masses. -/
theorem evenSymmetricMass_center_sub_le {n d : ℕ}
    (hn : 0 < n) (hd : d < n) (hmoderate : 2 * d ≤ n) :
    let E := 8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
      (1 : ℝ) / (6 * (n - d)) + (1 : ℝ) / (6 * n)
    0 ≤ evenSymmetricMass n 0 - evenSymmetricMass n d ∧
      evenSymmetricMass n 0 - evenSymmetricMass n d ≤
        ((d : ℝ) ^ 2 / n + E) * evenSymmetricMass n 0 := by
  dsimp only
  constructor
  · exact sub_nonneg.mpr (evenSymmetricMass_le_center n d)
  · have hr := evenSymmetricMass_ratio_gaussian_bounds hn hd hmoderate
    dsimp only at hr
    let E : ℝ := 8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
      (1 : ℝ) / (6 * (n - d)) + (1 : ℝ) / (6 * n)
    let g : ℝ := (d : ℝ) ^ 2 / n
    have hquot : Real.exp (-E) / Real.exp g ≤
        evenSymmetricMass n d / evenSymmetricMass n 0 := by
      apply (div_le_iff₀ (Real.exp_pos g)).2
      exact hr.1
    have hgauss : Real.exp (-(E + g)) ≤
        evenSymmetricMass n d / evenSymmetricMass n 0 := by
      rw [show -(E + g) = -E - g by ring, Real.exp_sub]
      exact hquot
    have hlinear : 1 - (E + g) ≤
        evenSymmetricMass n d / evenSymmetricMass n 0 :=
      (Real.one_sub_le_exp_neg (E + g)).trans hgauss
    have hloss : 1 - evenSymmetricMass n d / evenSymmetricMass n 0 ≤ E + g := by
      linarith
    have hcenter := evenSymmetricMass_pos (n := n) (d := 0) (by omega)
    change evenSymmetricMass n 0 - evenSymmetricMass n d ≤
      (g + E) * evenSymmetricMass n 0
    calc
      evenSymmetricMass n 0 - evenSymmetricMass n d =
          evenSymmetricMass n 0 *
            (1 - evenSymmetricMass n d / evenSymmetricMass n 0) := by
        field_simp
      _ ≤ evenSymmetricMass n 0 * (E + g) :=
        mul_le_mul_of_nonneg_left hloss hcenter.le
      _ = (g + E) * evenSymmetricMass n 0 := by ring

end Erdos1165.BinomialGaussian
