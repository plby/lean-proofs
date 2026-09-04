/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import ErdosProblems.Erdos230.GaussianCutoff

/-!
# Gaussian--Poisson aliases for Erdős Problem 230

This file contains the analytic core of the Gaussian-smoothed chirp
construction.  Our exponential convention is `e x = exp (2 * π * I * x)`.
-/

open scoped BigOperators Interval
open MeasureTheory Set Real Complex

noncomputable section

namespace Erdos230.GaussianPoisson

/-- The number-theorists' exponential `exp (2 π i x)`. -/
def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

@[simp] theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  simp

/-- Centre of the `h`-th Poisson alias. -/
def aliasCenter (n θ : ℝ) (h : ℤ) : ℝ := n * ((h : ℝ) + 1 / 2 - θ)

/-- Width of the positive Gaussian majorant of an alias. -/
def aliasWidthSq (n r : ℝ) : ℝ := n * (1 + r ^ 2) / r

/-- The positive Gaussian which majorizes the `h`-th alias integrand. -/
def aliasMajorant (n r θ : ℝ) (h : ℤ) (y : ℝ) : ℝ :=
  Real.exp
    (-π * (y - aliasCenter n θ h) ^ 2 /
      aliasWidthSq n r)

/-- The translate-free Gaussian used to bound every alias. -/
def majorantGaussian (n r t : ℝ) : ℝ :=
  Real.exp (-π * t ^ 2 / aliasWidthSq n r)

/-- The interval supporting the translated majorant of the `h`-th alias. -/
def aliasInterval (n K θ : ℝ) (h : ℤ) : Set ℝ :=
  Set.Ioc (K - aliasCenter n θ h) (n - K - aliasCenter n θ h)

/-- Oscillatory integral occurring in one Gaussian--Poisson alias. -/
def aliasIntegral (n r K θ : ℝ) (h : ℤ) : ℂ :=
  ∫ y in K..n - K,
    Complex.exp
      (π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
        (n * (1 - Complex.I * r)))

/-- The pointwise integrand of a normalized Poisson alias. -/
def aliasAtom (n r θ y : ℝ) (h : ℤ) : ℂ :=
  e (-(aliasCenter n θ h) ^ 2 / (2 * n)) /
      (1 - Complex.I * r) ^ (1 / 2 : ℂ) *
    Complex.exp
      (π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
        (n * (1 - Complex.I * r)))

/-- The normalized `h`-th alias. -/
def aliasTerm (n r K θ : ℝ) (h : ℤ) : ℂ :=
  e (-(aliasCenter n θ h) ^ 2 / (2 * n)) /
      (1 - Complex.I * r) ^ (1 / 2 : ℂ) *
    aliasIntegral n r K θ h

/-- The full Poisson-alias expansion of the smoothed chirp. -/
def aliasSum (n r K θ : ℝ) : ℂ :=
  ∑' h : ℤ, aliasTerm n r K θ h

/-! The following raw theta-series formulation is convenient for connecting
the alias expansion to the Gaussian-smoothed coefficients. -/

/-- Quadratic parameter in Jacobi's theta transformation. -/
def thetaA (n s : ℝ) : ℂ :=
  (1 - Complex.I * ((s ^ 2 / n : ℝ) : ℂ)) / ((s ^ 2 : ℝ) : ℂ)

/-- Linear parameter in Jacobi's theta transformation. -/
def thetaB (s θ y : ℝ) : ℂ :=
  y / s ^ 2 + Complex.I * (θ - 1 / 2)

/-- The Gaussian-smoothed chirp summand before applying the theta identity. -/
def gaussianChirpAtom (n s θ y : ℝ) (k : ℤ) : ℂ :=
  (s : ℂ)⁻¹ * Complex.exp
    (-π / s ^ 2 * ((k : ℂ) - y) ^ 2 +
      π * Complex.I / n * (k : ℂ) ^ 2 +
      2 * π * Complex.I * (θ - 1 / 2) * k)

/-- The normalized real Gaussian kernel used in the cutoff. -/
def gaussianKernel (s x : ℝ) : ℝ :=
  s⁻¹ * Real.exp (-π / s ^ 2 * x ^ 2)

/-- The Gaussian smoothing of the interval `[K,n-K]`, at an integer sample. -/
def gaussianCutoff (s K n : ℝ) (k : ℤ) : ℝ :=
  ∫ y in K..n - K, gaussianKernel s ((k : ℝ) - y)

/-- The quadratic chirp phase attached to the `k`-th coefficient. -/
def chirpPhase (n θ : ℝ) (k : ℤ) : ℝ :=
  (k : ℝ) ^ 2 / (2 * n) + (θ - 1 / 2) * k

theorem gaussianChirpAtom_eq_cutoffIntegrand
    (n s θ y : ℝ) (k : ℤ) (hn : 0 < n) (hs : 0 < s) :
    gaussianChirpAtom n s θ y k =
      (gaussianKernel s ((k : ℝ) - y) : ℂ) * e (chirpPhase n θ k) := by
  simp only [gaussianChirpAtom, gaussianKernel, chirpPhase, e]
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  field_simp [hn.ne', hs.ne']
  ring

theorem norm_gaussianChirpAtom
    (n s θ y : ℝ) (k : ℤ) (hn : 0 < n) (hs : 0 < s) :
    ‖gaussianChirpAtom n s θ y k‖ =
      gaussianKernel s ((k : ℝ) - y) := by
  rw [gaussianChirpAtom_eq_cutoffIntegrand n s θ y k hn hs,
    norm_mul, norm_e, mul_one, Complex.norm_real,
    Real.norm_of_nonneg]
  exact mul_nonneg (inv_nonneg.mpr hs.le) (Real.exp_pos _).le

theorem gaussianKernel_eq_phi (s x : ℝ) (hs : 0 < s) :
    gaussianKernel s x = Erdos230.GaussianCutoff.phi s x := by
  unfold gaussianKernel Erdos230.GaussianCutoff.phi
  congr 2
  field_simp [hs.ne']

theorem gaussianCutoff_eq_chi (s : ℝ) (K n : ℕ) (k : ℤ)
    (hs : 0 < s) (hKn : K ≤ n) :
    gaussianCutoff s K n k = Erdos230.GaussianCutoff.chi s K n k := by
  simp only [gaussianCutoff, Erdos230.GaussianCutoff.chi,
    Nat.cast_sub hKn]
  apply intervalIntegral.integral_congr
  intro y _
  exact gaussianKernel_eq_phi s ((k : ℝ) - y) hs

theorem summable_chi_int (s : ℝ) (K n : ℕ)
    (hs : 0 < s) (hKn : 2 * K ≤ n) :
    Summable (fun k : ℤ => Erdos230.GaussianCutoff.chi s K n (k : ℝ)) := by
  have hrightTail : Summable (fun j : ℕ =>
      Erdos230.GaussianCutoff.chi s K n ((j + (n + 1) : ℕ) : ℝ)) := by
    convert Erdos230.GaussianCutoff.summable_outsideRight hs hKn using 1
    funext j
    simp only [Erdos230.GaussianCutoff.outsideRight]
    congr 2
    omega
  have hright : Summable (fun j : ℕ =>
      Erdos230.GaussianCutoff.chi s K n (j : ℝ)) :=
    (summable_nat_add_iff (n + 1)).mp hrightTail
  have hleft : Summable (fun j : ℕ =>
      Erdos230.GaussianCutoff.chi s K n (((-((j : ℤ) + 1) : ℤ) : ℝ))) := by
    convert Erdos230.GaussianCutoff.summable_outsideLeft hs hKn using 1
    funext j
    simp only [Erdos230.GaussianCutoff.outsideLeft]
    congr 2
    norm_cast
  exact hright.of_nat_of_neg_add_one hleft

/-- The coefficient-series term of the Gaussian-cutoff chirp. -/
def cutoffChirpTerm (s : ℝ) (K n : ℕ) (θ : ℝ) (k : ℤ) : ℂ :=
  (Erdos230.GaussianCutoff.chi s K n (k : ℝ) : ℂ) *
    e (chirpPhase n θ k)

/-- The cutoff chirp retaining exactly the integer frequencies `0,...,n`. -/
def finiteCutoffChirp (s : ℝ) (K n : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), cutoffChirpTerm s K n θ (k : ℤ)

theorem norm_cutoffChirpTerm (s : ℝ) (K n : ℕ) (θ : ℝ) (k : ℤ)
    (hs : 0 < s) (hKn : 2 * K ≤ n) :
    ‖cutoffChirpTerm s K n θ k‖ =
      Erdos230.GaussianCutoff.chi s K n (k : ℝ) := by
  rw [cutoffChirpTerm, norm_mul, norm_e, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Erdos230.GaussianCutoff.chi_nonneg hs hKn _)]

theorem summable_cutoffChirpTerm (s : ℝ) (K n : ℕ) (θ : ℝ)
    (hs : 0 < s) (hKn : 2 * K ≤ n) :
    Summable (cutoffChirpTerm s K n θ) := by
  apply Summable.of_norm
  exact (summable_chi_int s K n hs hKn).congr
    (fun k => (norm_cutoffChirpTerm s K n θ k hs hKn).symm)

theorem intervalIntegral_gaussianChirpAtom
    (n s K θ : ℝ) (k : ℤ) (hn : 0 < n) (hs : 0 < s) :
    (∫ y in K..n - K, gaussianChirpAtom n s θ y k) =
      (gaussianCutoff s K n k : ℂ) * e (chirpPhase n θ k) := by
  calc
    (∫ y in K..n - K, gaussianChirpAtom n s θ y k) =
        ∫ y in K..n - K,
          (gaussianKernel s ((k : ℝ) - y) : ℂ) * e (chirpPhase n θ k) := by
      apply intervalIntegral.integral_congr
      intro y _
      exact gaussianChirpAtom_eq_cutoffIntegrand n s θ y k hn hs
    _ = (∫ y in K..n - K,
          (gaussianKernel s ((k : ℝ) - y) : ℂ)) * e (chirpPhase n θ k) := by
      rw [intervalIntegral.integral_mul_const]
    _ = _ := by
      rw [intervalIntegral.integral_ofReal]
      rfl

theorem finset_cutoffChirp_eq_integral
    (n s K θ : ℝ) (S : Finset ℤ) (hn : 0 < n) (hs : 0 < s) :
    (∑ k ∈ S, (gaussianCutoff s K n k : ℂ) * e (chirpPhase n θ k)) =
      ∫ y in K..n - K, ∑ k ∈ S, gaussianChirpAtom n s θ y k := by
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (show Continuous (gaussianChirpAtom n s θ · k) by
      unfold gaussianChirpAtom
      fun_prop).intervalIntegrable (μ := volume) K (n - K))]
  apply Finset.sum_congr rfl
  intro k _
  exact (intervalIntegral_gaussianChirpAtom n s K θ k hn hs).symm

/-- The `h`-th raw theta-transform summand at the smoothing point `y`. -/
def thetaAliasAtom (n s θ y : ℝ) (h : ℤ) : ℂ :=
  ((s : ℂ)⁻¹ * Complex.exp (-π * y ^ 2 / s ^ 2) /
      thetaA n s ^ (1 / 2 : ℂ)) *
    Complex.exp
      (-π / thetaA n s * ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2)

/-- The full integer Gaussian-smoothed chirp, written before Poisson
summation as the integral of its absolutely convergent theta series. -/
def fullIntegerSmoothedChirp (n s K θ : ℝ) : ℂ :=
  ∫ y in K..n - K, ∑' k : ℤ, gaussianChirpAtom n s θ y k

/-- The pointwise Jacobi transformation of the smoothed chirp. -/
theorem tsum_gaussianChirpAtom_eq_tsum_thetaAliasAtom
    (n s θ y : ℝ) (hn : 0 < n) (hs : 0 < s) :
    (∑' k : ℤ, gaussianChirpAtom n s θ y k) =
      ∑' h : ℤ, thetaAliasAtom n s θ y h := by
  have ha : 0 < (thetaA n s).re := by
    have heq : (thetaA n s).re = 1 / s ^ 2 := by
      simp only [thetaA, Complex.div_re]
      simp only [pow_two,
        Complex.ofReal_re, Complex.ofReal_im]
      norm_num [Complex.normSq]
    rw [heq]
    positivity
  calc
    (∑' k : ℤ, gaussianChirpAtom n s θ y k) =
        ((s : ℂ)⁻¹ * Complex.exp (-π * y ^ 2 / s ^ 2)) *
          ∑' k : ℤ, Complex.exp
            (-π * thetaA n s * (k : ℂ) ^ 2 +
              2 * π * thetaB s θ y * k) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      simp only [gaussianChirpAtom, thetaA, thetaB]
      conv_rhs => rw [mul_assoc, ← Complex.exp_add]
      congr 1
      congr 1
      simp only [← Complex.ofReal_pow]
      field_simp [hs.ne', hn.ne']
      push_cast
      field_simp [hn.ne']
      ring
    _ = ((s : ℂ)⁻¹ * Complex.exp (-π * y ^ 2 / s ^ 2)) *
        (1 / thetaA n s ^ (1 / 2 : ℂ) *
          ∑' h : ℤ, Complex.exp
            (-π / thetaA n s *
              ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2)) := by
      rw [Complex.tsum_exp_neg_quadratic ha (thetaB s θ y)]
    _ = ∑' h : ℤ, thetaAliasAtom n s θ y h := by
      rw [← tsum_mul_left, ← tsum_mul_left]
      apply tsum_congr
      intro h
      simp only [thetaAliasAtom]
      ring

theorem thetaAlias_exponent_eq_alias_exponent
    (n s θ y : ℝ) (h : ℤ) (hn : 0 < n) (hs : 0 < s) :
    -π * y ^ 2 / s ^ 2 -
        π / thetaA n s * ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2 =
      -π * Complex.I * aliasCenter n θ h ^ 2 / n +
        π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
          (n * (1 - Complex.I * (s ^ 2 / n))) := by
  have hden : (-(s : ℂ) ^ 2 * Complex.I + n) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    have : n = 0 := by simpa [pow_two] using hre
    exact hn.ne' this
  have hdenN : (n - (s : ℂ) ^ 2 * Complex.I) ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hden
  have hdenUnit : (1 - Complex.I * ((s ^ 2 / n : ℝ) : ℂ)) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    norm_num [pow_two] at hre
  simp only [thetaA, thetaB, aliasCenter]
  simp only [← Complex.ofReal_pow]
  field_simp [hn.ne', hs.ne', hden, hdenN, hdenUnit]
  push_cast
  field_simp [hn.ne', hs.ne', hden, hdenN, hdenUnit]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = -Complex.I := by rw [Complex.I_sq]; ring
  have hI4 : Complex.I ^ 4 = 1 := by
    calc
      Complex.I ^ 4 = Complex.I ^ 2 * Complex.I ^ 2 := by ring
      _ = 1 := by rw [Complex.I_sq]; ring
  have hI5 : Complex.I ^ 5 = Complex.I := by
    calc
      Complex.I ^ 5 = Complex.I ^ 4 * Complex.I := by ring
      _ = Complex.I := by rw [hI4]; ring
  ring_nf
  rw [hI3, hI4, hI5, Complex.I_sq]
  ring

theorem norm_one_sub_I_mul (r : ℝ) :
    ‖1 - Complex.I * r‖ = Real.sqrt (1 + r ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  norm_num [Complex.normSq]
  ring

theorem norm_thetaA (n s : ℝ) (hs : 0 < s) :
    ‖thetaA n s‖ =
      Real.sqrt (1 + (s ^ 2 / n) ^ 2) / s ^ 2 := by
  rw [thetaA, norm_div, norm_one_sub_I_mul]
  rw [show ‖((s ^ 2 : ℝ) : ℂ)‖ = s ^ 2 by
    rw [Complex.norm_real, Real.norm_of_nonneg]
    positivity]

theorem thetaA_cpow_half (n s : ℝ) (hs : 0 < s) :
    thetaA n s ^ (1 / 2 : ℂ) =
      (s : ℂ)⁻¹ * (1 - Complex.I * (s ^ 2 / n)) ^ (1 / 2 : ℂ) := by
  let z : ℂ := 1 - Complex.I * ((s ^ 2 / n : ℝ) : ℂ)
  have hz : z ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [z, pow_two] at hre
  have hs2 : 0 < s⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hs)
  have hfac : thetaA n s = ((s⁻¹ ^ 2 : ℝ) : ℂ) * z := by
    simp only [thetaA, z]
    field_simp [hs.ne']
    push_cast
    field_simp [hs.ne']
  rw [hfac]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hs2.ne') hz)]
  rw [Complex.log_ofReal_mul hs2 hz]
  rw [add_mul, Complex.exp_add]
  rw [← Complex.cpow_def_of_ne_zero hz]
  have hreal : (((s⁻¹ ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = (s : ℂ)⁻¹ := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_cpow hs2.le]
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (inv_nonneg.mpr hs.le)]
    push_cast
    rfl
  have hlog : Complex.log ((s⁻¹ ^ 2 : ℝ) : ℂ) =
      (Real.log (s⁻¹ ^ 2) : ℝ) := by
    simpa using Complex.log_ofReal_mul hs2 (one_ne_zero : (1 : ℂ) ≠ 0)
  have hexp : Complex.exp
      ((Real.log (s⁻¹ ^ 2) : ℂ) * (1 / 2 : ℂ)) =
      (((s⁻¹ ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hs2.ne'), hlog]
  rw [hexp, hreal]
  congr 1
  simp only [z]
  push_cast
  rfl

theorem thetaAliasAtom_eq_aliasAtom
    (n s θ y : ℝ) (h : ℤ) (hn : 0 < n) (hs : 0 < s) :
    thetaAliasAtom n s θ y h = aliasAtom n (s ^ 2 / n) θ y h := by
  let z : ℂ := 1 - Complex.I * ((s ^ 2 / n : ℝ) : ℂ)
  have hz : z ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [z, pow_two] at hre
  have hzpow : z ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)]
    exact hz
  calc
    thetaAliasAtom n s θ y h =
        (Complex.exp (-π * y ^ 2 / s ^ 2) / z ^ (1 / 2 : ℂ)) *
          Complex.exp
            (-π / thetaA n s * ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2) := by
      rw [thetaAliasAtom, thetaA_cpow_half n s hs]
      simp only [z]
      field_simp [hs.ne', hzpow]
      push_cast
      congr 2
      all_goals ring
    _ = 1 / z ^ (1 / 2 : ℂ) * Complex.exp
        (-π * y ^ 2 / s ^ 2 -
          π / thetaA n s * ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2) := by
      rw [div_eq_mul_inv]
      calc
        Complex.exp (-π * y ^ 2 / s ^ 2) * (z ^ (1 / 2 : ℂ))⁻¹ *
            Complex.exp
              (-π / thetaA n s * ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2) =
            (z ^ (1 / 2 : ℂ))⁻¹ *
              (Complex.exp (-π * y ^ 2 / s ^ 2) *
                Complex.exp
                  (-π / thetaA n s *
                    ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2)) := by ring
        _ = _ := by
          rw [← Complex.exp_add]
          ring_nf
    _ = 1 / z ^ (1 / 2 : ℂ) * Complex.exp
        (-π * Complex.I * aliasCenter n θ h ^ 2 / n +
          π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
            (n * (1 - Complex.I * (s ^ 2 / n)))) := by
      rw [thetaAlias_exponent_eq_alias_exponent n s θ y h hn hs]
    _ = aliasAtom n (s ^ 2 / n) θ y h := by
      rw [Complex.exp_add]
      have he : e (-(aliasCenter n θ h) ^ 2 / (2 * n)) =
          Complex.exp (-π * Complex.I * aliasCenter n θ h ^ 2 / n) := by
        simp only [e]
        congr 1
        push_cast
        field_simp [hn.ne']
      rw [aliasAtom, he]
      simp only [z]
      push_cast
      field_simp [hn.ne']

theorem gaussianExponent_re (n r A : ℝ) (hn : 0 < n) :
    (π * Complex.I * (A : ℂ) / (n * (1 - Complex.I * r))).re =
      -π * A * r / (n * (1 + r ^ 2)) := by
  rw [Complex.div_re]
  norm_num [Complex.normSq]
  field_simp

theorem norm_aliasIntegrand (n r θ y : ℝ) (h : ℤ)
    (hn : 0 < n) (hr : 0 < r) :
    ‖Complex.exp
      (π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
        (n * (1 - Complex.I * r)))‖ =
      Real.exp
        (-π * (y - aliasCenter n θ h) ^ 2 /
          aliasWidthSq n r) := by
  have hcast :
      (((y : ℂ) - (aliasCenter n θ h : ℂ)) ^ 2) =
        (((y - aliasCenter n θ h) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  rw [Complex.norm_exp]
  rw [gaussianExponent_re n r _ hn]
  congr 1
  simp only [aliasWidthSq]
  field_simp

theorem intervalIntegral_aliasAtom (n r K θ : ℝ) (h : ℤ) :
    (∫ y in K..n - K, aliasAtom n r θ y h) = aliasTerm n r K θ h := by
  unfold aliasAtom aliasTerm aliasIntegral
  rw [intervalIntegral.integral_const_mul]

theorem norm_aliasIntegral_le (n r K θ : ℝ) (h : ℤ)
    (hn : 0 < n) (hr : 0 < r) (hK : K ≤ n - K) :
    ‖aliasIntegral n r K θ h‖ ≤
      ∫ y in K..n - K, aliasMajorant n r θ h y := by
  refine (intervalIntegral.norm_integral_le_integral_norm hK).trans_eq ?_
  apply intervalIntegral.integral_congr
  intro y _
  exact norm_aliasIntegrand n r θ y h hn hr

theorem integral_aliasMajorant_eq (n r K θ : ℝ) (h : ℤ) :
    (∫ y in K..n - K, aliasMajorant n r θ h y) =
      ∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
        Real.exp (-π * t ^ 2 / aliasWidthSq n r) := by
  simpa only [aliasMajorant] using
    intervalIntegral.integral_comp_sub_right
      (fun t : ℝ => Real.exp (-π * t ^ 2 / aliasWidthSq n r))
      (aliasCenter n θ h)

theorem aliasWidthSq_pos (n r : ℝ) (hn : 0 < n) (hr : 0 < r) :
    0 < aliasWidthSq n r := by
  exact div_pos (mul_pos hn (by positivity)) hr

theorem integrable_majorantGaussian (n r : ℝ) (hn : 0 < n) (hr : 0 < r) :
    Integrable (majorantGaussian n r) := by
  have hb : 0 < π / aliasWidthSq n r :=
    div_pos Real.pi_pos (aliasWidthSq_pos n r hn hr)
  rw [show majorantGaussian n r =
      (fun x : ℝ => Real.exp (-(π / aliasWidthSq n r) * x ^ 2)) by
    funext x
    simp only [majorantGaussian]
    congr 1
    ring]
  exact integrable_exp_neg_mul_sq hb

theorem pairwise_disjoint_aliasInterval (n K θ : ℝ)
    (hn : 0 < n) (hK : 0 ≤ K) :
    Pairwise (fun h j : ℤ =>
      Disjoint (aliasInterval n K θ h) (aliasInterval n K θ j)) := by
  intro h j hne
  rcases lt_or_gt_of_ne hne with hhj | hjh
  · exact (Set.Ioc_disjoint_Ioc_of_le (a := K - aliasCenter n θ j)
      (b := n - K - aliasCenter n θ j)
      (c := K - aliasCenter n θ h)
      (d := n - K - aliasCenter n θ h) (by
        simp only [aliasCenter]
        have hcast : (h : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hhj
        nlinarith)).symm
  · apply Set.Ioc_disjoint_Ioc_of_le
    simp only [aliasCenter]
    have hcast : (j : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast hjh
    nlinarith

theorem tsum_integral_majorant_le_integral (n r K θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    (∑' h : ℤ,
      ∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
        majorantGaussian n r t) ≤
      ∫ t : ℝ, majorantGaussian n r t := by
  have hle (h : ℤ) :
      K - aliasCenter n θ h ≤ n - K - aliasCenter n θ h := by
    linarith
  simp_rw [intervalIntegral.integral_of_le (hle _)]
  change (∑' h : ℤ, ∫ t in aliasInterval n K θ h,
    majorantGaussian n r t) ≤ _
  rw [← MeasureTheory.integral_iUnion
    (s := aliasInterval n K θ)
    (f := majorantGaussian n r)
    (fun _ => measurableSet_Ioc)
    (pairwise_disjoint_aliasInterval n K θ hn hK0)
    ((integrable_majorantGaussian n r hn hr).integrableOn)]
  exact MeasureTheory.setIntegral_le_integral
    (integrable_majorantGaussian n r hn hr)
    (ae_of_all _ fun _ => Real.exp_pos _ |>.le)

theorem integral_majorantGaussian (n r : ℝ) (hn : 0 < n) (hr : 0 < r) :
    (∫ t : ℝ, majorantGaussian n r t) = Real.sqrt (aliasWidthSq n r) := by
  have hw : aliasWidthSq n r ≠ 0 := ne_of_gt (aliasWidthSq_pos n r hn hr)
  rw [show majorantGaussian n r =
      (fun x : ℝ => Real.exp (-(π / aliasWidthSq n r) * x ^ 2)) by
    funext x
    simp only [majorantGaussian]
    congr 1
    ring]
  rw [integral_gaussian]
  congr 1
  field_simp

theorem norm_one_sub_I_mul_cpow_half (r : ℝ) :
    ‖(1 - Complex.I * r) ^ (1 / 2 : ℂ)‖ =
      (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  rw [Complex.norm_cpow_real, Complex.norm_def]
  simp only [Complex.normSq_apply]
  norm_num
  have hb : 0 ≤ 1 + r * r := by nlinarith [sq_nonneg r]
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hb]
  norm_num
  simp only [pow_two]

theorem norm_aliasAtom (n r θ y : ℝ) (h : ℤ)
    (hn : 0 < n) (hr : 0 < r) :
    ‖aliasAtom n r θ y h‖ =
      aliasMajorant n r θ h y / (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  calc
    ‖aliasAtom n r θ y h‖ =
        1 / (1 + r ^ 2) ^ (1 / 4 : ℝ) *
          ‖Complex.exp
            (π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
              (n * (1 - Complex.I * r)))‖ := by
      rw [aliasAtom, norm_mul, norm_div, norm_e,
        norm_one_sub_I_mul_cpow_half]
    _ = 1 / (1 + r ^ 2) ^ (1 / 4 : ℝ) *
        aliasMajorant n r θ h y := by
      rw [norm_aliasIntegrand n r θ y h hn hr]
      rfl
    _ = _ := by ring

theorem norm_aliasTerm_le (n r K θ : ℝ) (h : ℤ)
    (hn : 0 < n) (hr : 0 < r) (hK : K ≤ n - K) :
    ‖aliasTerm n r K θ h‖ ≤
      (∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
        majorantGaussian n r t) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  calc
    ‖aliasTerm n r K θ h‖ =
        ‖aliasIntegral n r K θ h‖ / (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
      rw [aliasTerm, norm_mul, norm_div, norm_e,
        norm_one_sub_I_mul_cpow_half]
      ring
    _ ≤ (∫ y in K..n - K, aliasMajorant n r θ h y) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
      exact div_le_div_of_nonneg_right
        (norm_aliasIntegral_le n r K θ h hn hr hK) (by positivity)
    _ = _ := by
      rw [integral_aliasMajorant_eq]
      rfl

theorem summable_interval_majorant (n r K θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    Summable (fun h : ℤ =>
      ∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
        majorantGaussian n r t) := by
  have hle (h : ℤ) :
      K - aliasCenter n θ h ≤ n - K - aliasCenter n θ h := by
    linarith
  simp_rw [intervalIntegral.integral_of_le (hle _)]
  change Summable (fun h : ℤ =>
    ∫ t in aliasInterval n K θ h, majorantGaussian n r t)
  exact (MeasureTheory.hasSum_integral_iUnion
    (s := aliasInterval n K θ)
    (f := majorantGaussian n r)
    (fun _ => measurableSet_Ioc)
    (pairwise_disjoint_aliasInterval n K θ hn hK0)
    ((integrable_majorantGaussian n r hn hr).integrableOn)).summable

theorem summable_norm_aliasTerm (n r K θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    Summable (fun h : ℤ => ‖aliasTerm n r K θ h‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun h => norm_aliasTerm_le n r K θ h hn hr hK)
  exact (summable_interval_majorant n r K θ hn hr hK0 hK).div_const _

theorem tsum_norm_aliasTerm_le (n r K θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    (∑' h : ℤ, ‖aliasTerm n r K θ h‖) ≤
      Real.sqrt (aliasWidthSq n r) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  calc
    (∑' h : ℤ, ‖aliasTerm n r K θ h‖) ≤
        ∑' h : ℤ,
          (∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
            majorantGaussian n r t) /
              (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
      exact Summable.tsum_le_tsum
        (fun h => norm_aliasTerm_le n r K θ h hn hr hK)
        (summable_norm_aliasTerm n r K θ hn hr hK0 hK)
        ((summable_interval_majorant n r K θ hn hr hK0 hK).div_const _)
    _ = (∑' h : ℤ,
          ∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
            majorantGaussian n r t) /
              (1 + r ^ 2) ^ (1 / 4 : ℝ) := tsum_div_const
    _ ≤ (∫ t : ℝ, majorantGaussian n r t) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
      exact div_le_div_of_nonneg_right
        (tsum_integral_majorant_le_integral n r K θ hn hr hK0 hK)
        (by positivity)
    _ = _ := by rw [integral_majorantGaussian n r hn hr]

theorem norm_aliasSum_le (n r K θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    ‖aliasSum n r K θ‖ ≤
      Real.sqrt (aliasWidthSq n r) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  calc
    ‖aliasSum n r K θ‖ ≤ ∑' h : ℤ, ‖aliasTerm n r K θ h‖ := by
      exact norm_tsum_le_tsum_norm
        (summable_norm_aliasTerm n r K θ hn hr hK0 hK)
    _ ≤ _ := tsum_norm_aliasTerm_le n r K θ hn hr hK0 hK

theorem hasSum_aliasTerm_fullIntegerSmoothedChirp
    (n s K θ : ℝ) (hn : 0 < n) (hs : 0 < s)
    (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    HasSum (fun h : ℤ => aliasTerm n (s ^ 2 / n) K θ h)
      (fullIntegerSmoothedChirp n s K θ) := by
  let r : ℝ := s ^ 2 / n
  have hr : 0 < r := div_pos (sq_pos_of_pos hs) hn
  let D : ℝ := (1 + r ^ 2) ^ (1 / 4 : ℝ)
  have hFint (h : ℤ) :
      Integrable (aliasAtom n r θ · h)
        (volume.restrict (Set.Ioc K (n - K))) := by
    have hi := (show Continuous (aliasAtom n r θ · h) by
      unfold aliasAtom e aliasCenter
      fun_prop).intervalIntegrable (μ := volume) K (n - K)
    rw [intervalIntegrable_iff, uIoc_of_le hK] at hi
    exact hi
  have hmass : Summable (fun h : ℤ =>
      (∫ y in Set.Ioc K (n - K), ‖aliasAtom n r θ y h‖) ) := by
    have hbase := (summable_interval_majorant n r K θ hn hr hK0 hK).div_const D
    exact hbase.congr (fun h => by
      rw [← intervalIntegral.integral_of_le hK]
      rw [show (∫ y in K..n - K, ‖aliasAtom n r θ y h‖) =
          ∫ y in K..n - K, aliasMajorant n r θ h y / D by
        apply intervalIntegral.integral_congr
        intro y _
        exact norm_aliasAtom n r θ y h hn hr]
      rw [intervalIntegral.integral_div]
      rw [integral_aliasMajorant_eq]
      rfl)
  have hswap := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc K (n - K))) hFint hmass
  have hfull : fullIntegerSmoothedChirp n s K θ =
      ∫ y in Set.Ioc K (n - K), ∑' h : ℤ, aliasAtom n r θ y h := by
    unfold fullIntegerSmoothedChirp
    rw [intervalIntegral.integral_of_le hK]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro y _
    change (∑' k : ℤ, gaussianChirpAtom n s θ y k) =
      ∑' h : ℤ, aliasAtom n r θ y h
    rw [tsum_gaussianChirpAtom_eq_tsum_thetaAliasAtom n s θ y hn hs]
    apply tsum_congr
    intro h
    simpa only [r] using thetaAliasAtom_eq_aliasAtom n s θ y h hn hs
  rw [hfull]
  have hterm : (fun h : ℤ =>
      ∫ y in Set.Ioc K (n - K), aliasAtom n r θ y h) =
      (fun h : ℤ => aliasTerm n (s ^ 2 / n) K θ h) := by
    funext h
    rw [← intervalIntegral_aliasAtom n r K θ h]
    rw [intervalIntegral.integral_of_le hK]
  rw [← hterm]
  exact hswap

theorem fullIntegerSmoothedChirp_eq_aliasSum
    (n s K θ : ℝ) (hn : 0 < n) (hs : 0 < s)
    (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    fullIntegerSmoothedChirp n s K θ = aliasSum n (s ^ 2 / n) K θ := by
  exact (hasSum_aliasTerm_fullIntegerSmoothedChirp n s K θ hn hs hK0 hK).tsum_eq.symm

theorem norm_fullIntegerSmoothedChirp_le
    (n s K θ : ℝ) (hn : 0 < n) (hs : 0 < s)
    (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    ‖fullIntegerSmoothedChirp n s K θ‖ ≤
      Real.sqrt (aliasWidthSq n (s ^ 2 / n)) /
        (1 + (s ^ 2 / n) ^ 2) ^ (1 / 4 : ℝ) := by
  rw [fullIntegerSmoothedChirp_eq_aliasSum n s K θ hn hs hK0 hK]
  exact norm_aliasSum_le n (s ^ 2 / n) K θ hn
    (div_pos (sq_pos_of_pos hs) hn) hK0 hK

theorem aliasBound_eq (n r : ℝ) (hn : 0 < n) (hr : 0 < r) :
    Real.sqrt (aliasWidthSq n r) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) =
      Real.sqrt n * (1 + r⁻¹ ^ 2) ^ (1 / 4 : ℝ) := by
  have hB : 0 < 1 + r ^ 2 := by positivity
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [aliasWidthSq, Real.div_rpow (mul_nonneg hn.le hB.le) hr.le]
  rw [Real.mul_rpow hn.le hB.le]
  have hBpow : (1 + r ^ 2) ^ (1 / 2 : ℝ) /
      (1 + r ^ 2) ^ (1 / 4 : ℝ) = (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_sub hB]
    norm_num
  rw [show n ^ (1 / 2 : ℝ) * (1 + r ^ 2) ^ (1 / 2 : ℝ) /
      r ^ (1 / 2 : ℝ) / (1 + r ^ 2) ^ (1 / 4 : ℝ) =
      n ^ (1 / 2 : ℝ) / r ^ (1 / 2 : ℝ) *
        ((1 + r ^ 2) ^ (1 / 2 : ℝ) /
          (1 + r ^ 2) ^ (1 / 4 : ℝ)) by ring]
  rw [hBpow]
  rw [show 1 + r⁻¹ ^ 2 = (1 + r ^ 2) / r ^ 2 by
    field_simp [hr.ne']
    ring]
  rw [Real.div_rpow hB.le hr2.le]
  rw [show (r ^ 2) ^ (1 / 4 : ℝ) = r ^ (1 / 2 : ℝ) by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num]
  ring

theorem norm_fullIntegerSmoothedChirp_le_exact
    (n s K θ : ℝ) (hn : 0 < n) (hs : 0 < s)
    (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    ‖fullIntegerSmoothedChirp n s K θ‖ ≤
      Real.sqrt n * (1 + (s ^ 2 / n)⁻¹ ^ 2) ^ (1 / 4 : ℝ) := by
  rw [← aliasBound_eq n (s ^ 2 / n) hn
    (div_pos (sq_pos_of_pos hs) hn)]
  exact norm_fullIntegerSmoothedChirp_le n s K θ hn hs hK0 hK

theorem fullIntegerSmoothedChirp_eq_tsum_cutoffChirpTerm
    (s : ℝ) (K n : ℕ) (θ : ℝ) (hs : 0 < s) (hn0 : 0 < n)
    (hKn : 2 * K ≤ n) :
    fullIntegerSmoothedChirp n s K θ =
      ∑' k : ℤ, cutoffChirpTerm s K n θ k := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast hn0
  have hKle : K ≤ n := by omega
  have horder : (K : ℝ) ≤ (n : ℝ) - K := by
    rw [← Nat.cast_sub hKle]
    exact Erdos230.GaussianCutoff.cutoff_endpoints_order hKn
  have hFint (k : ℤ) :
      Integrable (gaussianChirpAtom n s θ · k)
        (volume.restrict (Set.Ioc K ((n : ℝ) - K))) := by
    have hi := (show Continuous (gaussianChirpAtom n s θ · k) by
      unfold gaussianChirpAtom
      fun_prop).intervalIntegrable (μ := volume) (K : ℝ) ((n : ℝ) - K)
    rw [intervalIntegrable_iff, uIoc_of_le horder] at hi
    exact hi
  have hmass : Summable (fun k : ℤ =>
      ∫ y in Set.Ioc (K : ℝ) ((n : ℝ) - K),
        ‖gaussianChirpAtom n s θ y k‖) := by
    exact (summable_chi_int s K n hs hKn).congr (fun k => by
      symm
      rw [← intervalIntegral.integral_of_le horder]
      calc
        (∫ y in (K : ℝ)..(n : ℝ) - K,
            ‖gaussianChirpAtom n s θ y k‖) =
            ∫ y in (K : ℝ)..(n : ℝ) - K,
              gaussianKernel s ((k : ℝ) - y) := by
          apply intervalIntegral.integral_congr
          intro y _
          exact norm_gaussianChirpAtom n s θ y k hn hs
        _ = gaussianCutoff s K n k := rfl
        _ = Erdos230.GaussianCutoff.chi s K n (k : ℝ) :=
          gaussianCutoff_eq_chi s K n k hs (by omega))
  have hswap := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (K : ℝ) ((n : ℝ) - K))) hFint hmass
  have hfull : fullIntegerSmoothedChirp n s K θ =
      ∫ y in Set.Ioc (K : ℝ) ((n : ℝ) - K),
        ∑' k : ℤ, gaussianChirpAtom n s θ y k := by
    unfold fullIntegerSmoothedChirp
    rw [intervalIntegral.integral_of_le horder]
  have hterm : (fun k : ℤ =>
      ∫ y in Set.Ioc (K : ℝ) ((n : ℝ) - K),
        gaussianChirpAtom n s θ y k) = cutoffChirpTerm s K n θ := by
    funext k
    rw [← intervalIntegral.integral_of_le horder]
    rw [intervalIntegral_gaussianChirpAtom n s K θ k hn hs]
    rw [gaussianCutoff_eq_chi s K n k hs (by omega)]
    rfl
  rw [hfull]
  rw [← hterm]
  exact hswap.tsum_eq.symm

theorem norm_finiteCutoffChirp_sub_full_le_outside
    (s : ℝ) (K n : ℕ) (θ : ℝ) (hs : 0 < s) (hn0 : 0 < n)
    (hKn : 2 * K ≤ n) :
    ‖finiteCutoffChirp s K n θ - fullIntegerSmoothedChirp n s K θ‖ ≤
      (∑' j : ℕ, Erdos230.GaussianCutoff.outsideLeft s K n j) +
        ∑' j : ℕ, Erdos230.GaussianCutoff.outsideRight s K n j := by
  let f : ℤ → ℂ := cutoffChirpTerm s K n θ
  let right : ℕ → ℂ := fun j => f (j + (n + 1) : ℕ)
  let left : ℕ → ℂ := fun j => f (-((j : ℤ) + 1))
  have hrightNorm : Summable (fun j : ℕ => ‖right j‖) := by
    exact (Erdos230.GaussianCutoff.summable_outsideRight hs hKn).congr (fun j => by
      symm
      simp only [right, f, norm_cutoffChirpTerm s K n θ _ hs hKn,
        Erdos230.GaussianCutoff.outsideRight]
      congr 2
      norm_cast
      omega)
  have hleftNorm : Summable (fun j : ℕ => ‖left j‖) := by
    exact (Erdos230.GaussianCutoff.summable_outsideLeft hs hKn).congr (fun j => by
      symm
      simp only [left, f, norm_cutoffChirpTerm s K n θ _ hs hKn,
        Erdos230.GaussianCutoff.outsideLeft]
      congr 2
      norm_cast)
  have hright : Summable right := Summable.of_norm hrightNorm
  have hleft : Summable left := Summable.of_norm hleftNorm
  have hnat : Summable (fun j : ℕ => f j) := by
    apply (summable_nat_add_iff (n + 1)).mp
    simpa only [right] using hright
  have hdecomp :
      (∑' k : ℤ, f k) = finiteCutoffChirp s K n θ +
          (∑' j : ℕ, right j) + ∑' j : ℕ, left j := by
    rw [tsum_of_nat_of_neg_add_one hnat hleft]
    rw [← hnat.sum_add_tsum_nat_add (n + 1)]
    simp only [finiteCutoffChirp, right, left, f]
  rw [fullIntegerSmoothedChirp_eq_tsum_cutoffChirpTerm s K n θ hs hn0 hKn]
  change ‖finiteCutoffChirp s K n θ - ∑' k : ℤ, f k‖ ≤ _
  rw [hdecomp]
  calc
    ‖finiteCutoffChirp s K n θ -
        (finiteCutoffChirp s K n θ + (∑' j : ℕ, right j) +
          ∑' j : ℕ, left j)‖ =
        ‖(∑' j : ℕ, right j) + ∑' j : ℕ, left j‖ := by
      rw [show finiteCutoffChirp s K n θ -
          (finiteCutoffChirp s K n θ + (∑' j : ℕ, right j) +
            ∑' j : ℕ, left j) =
          - ((∑' j : ℕ, right j) + ∑' j : ℕ, left j) by ring,
        norm_neg]
    _ ≤ ‖∑' j : ℕ, right j‖ + ‖∑' j : ℕ, left j‖ := norm_add_le _ _
    _ ≤ (∑' j : ℕ, ‖right j‖) + ∑' j : ℕ, ‖left j‖ := by
      exact add_le_add (norm_tsum_le_tsum_norm hrightNorm)
        (norm_tsum_le_tsum_norm hleftNorm)
    _ = (∑' j : ℕ, Erdos230.GaussianCutoff.outsideRight s K n j) +
        ∑' j : ℕ, Erdos230.GaussianCutoff.outsideLeft s K n j := by
      congr 1
      · apply tsum_congr
        intro j
        simp only [right, f, norm_cutoffChirpTerm s K n θ _ hs hKn,
          Erdos230.GaussianCutoff.outsideRight]
        congr 2
        norm_cast
        omega
      · apply tsum_congr
        intro j
        simp only [left, f, norm_cutoffChirpTerm s K n θ _ hs hKn,
          Erdos230.GaussianCutoff.outsideLeft]
        congr 2
        norm_cast
    _ = _ := by ring

end Erdos230.GaussianPoisson
