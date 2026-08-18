/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterKernelCoefficients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The localized product cosine kernel

This file identifies the finite coefficient array from
`HunterKernelCoefficients` with a power of a nonnegative cosine factor on
the unit circle.
-/

open Set Function MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate

namespace Erdos984

noncomputable section

lemma fourier_eq_zpow (n : ℤ) (x : UnitAddCircle) :
    fourier n x = (fourier 1 x) ^ n := by
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
      rw [fourier_coe_apply, fourier_coe_apply]
      rw [← Complex.exp_int_mul]
      congr 1
      push_cast
      ring

/-- The basic circle factor `(1 + cos(2πx))/2`, written algebraically in
terms of the unit complex character. -/
def circleCosSq (x : UnitAddCircle) : ℂ :=
  let z := fourier 1 x
  (1 + z) ^ 2 / (4 * z)

lemma circleCosSq_coe (x : ℝ) :
    circleCosSq (x : UnitAddCircle) =
      (((Real.cos (Real.pi * x)) ^ 2 : ℝ) : ℂ) := by
  rw [circleCosSq, fourier_coe_apply]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (x : ℂ) / (1 : ℝ) =
      2 * (Real.pi * x) * Complex.I by push_cast; ring]
  push_cast
  let y : ℂ := (Real.pi : ℂ) * (x : ℂ)
  let w : ℂ := Complex.exp (y * Complex.I)
  have hw : w ≠ 0 := Complex.exp_ne_zero _
  have htwo : Complex.exp (2 * y * Complex.I) = w ^ 2 := by
    rw [show 2 * y * Complex.I = y * Complex.I + y * Complex.I by ring,
      Complex.exp_add]
    simp [w, pow_two]
  change (1 + Complex.exp (2 * y * Complex.I)) ^ 2 /
      (4 * Complex.exp (2 * y * Complex.I)) = _
  rw [htwo]
  change (1 + w ^ 2) ^ 2 / (4 * w ^ 2) = Complex.cos y ^ 2
  rw [show Complex.cos y = (w + w⁻¹) / 2 by
    rw [Complex.cos]
    change (w + Complex.exp (-y * Complex.I)) / 2 = _
    rw [show -y * Complex.I = -(y * Complex.I) by ring, Complex.exp_neg]
  ]
  field_simp [hw]
  ring

lemma circleCosSq_real (x : UnitAddCircle) :
    (circleCosSq x).im = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
      have h := congrArg Complex.im (circleCosSq_coe x)
      simpa only [map_pow, Complex.ofReal_im] using h

lemma circleCosSq_nonneg (x : UnitAddCircle) :
    0 ≤ (circleCosSq x).re := by
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
      have h := congrArg Complex.re (circleCosSq_coe x)
      simp only [Complex.ofReal_re] at h
      rw [h]
      positivity

lemma pow_im_eq_zero_of_im_eq_zero (z : ℂ) (hz : z.im = 0) (k : ℕ) :
    (z ^ k).im = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Complex.mul_im, hz, ih]
      ring

/-- Product kernel on a finite unit torus. -/
def torusCosineKernel {D : Type*} [Fintype D] (k : ℕ)
    (x : UnitAddTorus D) : ℂ :=
  ∏ j, (circleCosSq (x j)) ^ k

lemma torusCosineKernel_real {D : Type*} [Fintype D] (k : ℕ)
    (x : UnitAddTorus D) : (torusCosineKernel k x).im = 0 := by
  classical
  rw [torusCosineKernel]
  induction (Finset.univ : Finset D) using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Complex.mul_im]
      have hpow : (circleCosSq (x j) ^ k).im = 0 :=
        pow_im_eq_zero_of_im_eq_zero _ (circleCosSq_real _) _
      rw [hpow, ih]
      ring

/-- The one-dimensional binomial identity underlying the kernel. -/
lemma sum_kernelDigitCoeff_zpow (k : ℕ) (z : ℂ) (hz : z ≠ 0) :
    ∑ q : HunterKernelDigit k,
      (kernelDigitCoeff k q : ℂ) * z ^ (decodeKernelDigit k q) =
      ((1 + z) ^ 2 / (4 * z)) ^ k := by
  simp_rw [kernelDigitCoeff, decodeKernelDigit]
  push_cast
  simp_rw [zpow_sub₀ hz, zpow_natCast]
  simp_rw [div_mul_div_comm]
  rw [← Finset.sum_div]
  have hsum : (∑ q : Fin (2 * k + 1),
      ((Nat.choose (2 * k) q.val : ℕ) : ℂ) * z ^ q.val) =
      (1 + z) ^ (2 * k) := by
    rw [add_comm 1 z, add_pow z 1]
    rw [← Fin.sum_univ_eq_sum_range]
    simp [mul_comm]
  rw [hsum]
  rw [div_pow, mul_pow, pow_mul]

/-- Exact finite Fourier expansion of the circle kernel. -/
lemma sum_kernelDigitCoeff_fourier (k : ℕ) (x : UnitAddCircle) :
    ∑ q : HunterKernelDigit k,
      (kernelDigitCoeff k q : ℂ) * fourier (decodeKernelDigit k q) x =
      circleCosSq x ^ k := by
  calc
    _ = ∑ q : HunterKernelDigit k,
        (kernelDigitCoeff k q : ℂ) *
          (fourier 1 x) ^ (decodeKernelDigit k q) := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [fourier_eq_zpow]
    _ = ((1 + fourier 1 x) ^ 2 / (4 * fourier 1 x)) ^ k :=
      sum_kernelDigitCoeff_zpow k _ (by
        rw [fourier_apply]
        exact Circle.coe_ne_zero _)
    _ = circleCosSq x ^ k := rfl

/-- Exact product Fourier expansion of the torus kernel. -/
lemma sum_kernelCoeff_torusFourier {D : Type*} [Fintype D]
    [DecidableEq D] (k : ℕ) (x : UnitAddTorus D) :
    ∑ q : D → HunterKernelDigit k,
      (kernelCoeff k q : ℂ) * torusFourier (kernelFrequency k q) x =
      torusCosineKernel k x := by
  rw [torusCosineKernel]
  simp_rw [← sum_kernelDigitCoeff_fourier]
  rw [Fintype.prod_sum]
  simp only [kernelCoeff, torusFourier, kernelFrequency]
  push_cast
  simp_rw [Finset.prod_mul_distrib]

end

end Erdos984
