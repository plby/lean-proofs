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

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gaussian quadratic polynomials

This file supplies the Gaussian and finite-matrix infrastructure used in the
Kwan--Sah--Sauermann--Sawhney proof of Erdős Problem 88.  In particular it
records the exact one-coordinate characteristic-function factor, the variance
bookkeeping for diagonal quadratic polynomials, and robust-rank/Frobenius
adapters.
-/

open scoped ENNReal NNReal Matrix.Norms.Frobenius
open MeasureTheory ProbabilityTheory Real Complex
open Polynomial

namespace Erdos88
namespace GaussianQuadratic

/-- The standard real Gaussian probability measure. -/
noncomputable abbrev standardGaussian : Measure ℝ := gaussianReal 0 1

/-- A single (not necessarily centered) diagonal quadratic Gaussian factor. -/
def coordinatePolynomial (a lam : ℝ) (x : ℝ) : ℝ := a * x + lam * x ^ 2

/-- The centered version of `coordinatePolynomial`. -/
def centeredCoordinatePolynomial (a lam : ℝ) (x : ℝ) : ℝ :=
  a * x + lam * (x ^ 2 - 1)

/-- Quadratic coefficient after the standard Gaussian density has been folded
into a characteristic-function integral. -/
private noncomputable def quadCoeff (lam t : ℝ) : ℂ :=
  (-1 / 2 : ℂ) + ((t * lam : ℝ) : ℂ) * I

/-- Linear coefficient after the standard Gaussian density has been folded
into a characteristic-function integral. -/
private def linCoeff (a t : ℝ) : ℂ := ((t * a : ℝ) : ℂ) * I

private lemma quadCoeff_re (lam t : ℝ) : (quadCoeff lam t).re = -1 / 2 := by
  simp [quadCoeff]

private lemma quadCoeff_re_neg (lam t : ℝ) : (quadCoeff lam t).re < 0 := by
  rw [quadCoeff_re]
  norm_num

/-- The complex Gaussian integral underlying KSSS (4.28).  This is the exact
one-coordinate characteristic-function factor before its norm is simplified.
The use of complex powers fixes the principal square-root branch. -/
theorem coordinate_charFactor_complex (a lam t : ℝ) :
    (∫ x : ℝ, cexp ((((t * coordinatePolynomial a lam x : ℝ) : ℂ) * I))
        ∂standardGaussian)
      = ((√(2 * π) : ℝ) : ℂ)⁻¹ *
          ((π : ℂ) / -(quadCoeff lam t)) ^ (1 / 2 : ℂ) *
            cexp (-((linCoeff a t) ^ 2 / (4 * quadCoeff lam t))) := by
  rw [integral_gaussianReal_eq_integral_smul (v := (1 : ℝ≥0)) one_ne_zero]
  calc
    (∫ x : ℝ, gaussianPDFReal 0 1 x •
        cexp ((((t * coordinatePolynomial a lam x : ℝ) : ℂ) * I)))
      = ((√(2 * π) : ℝ) : ℂ)⁻¹ *
          ∫ x : ℝ, cexp (quadCoeff lam t * (x : ℂ) ^ 2 + linCoeff a t * x) := by
        simp_rw [Complex.real_smul]
        unfold gaussianPDFReal
        push_cast
        simp_rw [mul_assoc, integral_const_mul, ← Complex.exp_add]
        simp only [mul_one]
        apply congrArg (fun z : ℂ ↦ ((↑√(2 * π) : ℂ)⁻¹ * z))
        apply integral_congr_ae
        filter_upwards [] with x
        apply congrArg cexp
        simp only [coordinatePolynomial, quadCoeff, linCoeff]
        push_cast
        ring
    _ = ((√(2 * π) : ℝ) : ℂ)⁻¹ *
          ((π : ℂ) / -(quadCoeff lam t)) ^ (1 / 2 : ℂ) *
            cexp (-((linCoeff a t) ^ 2 / (4 * quadCoeff lam t))) := by
        rw [show (∫ x : ℝ, cexp
              (quadCoeff lam t * (x : ℂ) ^ 2 + linCoeff a t * x)) =
            ((π : ℂ) / -(quadCoeff lam t)) ^ (1 / 2 : ℂ) *
              cexp (-((linCoeff a t) ^ 2 / (4 * quadCoeff lam t))) by
          simpa only [add_zero, zero_sub] using
            integral_cexp_quadratic (quadCoeff_re_neg lam t) (linCoeff a t) 0]
        ring

private lemma quadCoeff_ne_zero (lam t : ℝ) : quadCoeff lam t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [quadCoeff] at this

private lemma norm_quadCoeff (lam t : ℝ) :
    ‖quadCoeff lam t‖ = √(1 / 4 + (t * lam) ^ 2) := by
  rw [Complex.norm_def]
  apply congrArg (fun x : ℝ ↦ √x)
  simp only [Complex.normSq_apply, quadCoeff]
  simp
  ring

private lemma quadraticExponent_re (a lam t : ℝ) :
    (-((linCoeff a t) ^ 2 / (4 * quadCoeff lam t))).re =
      -(a ^ 2 * t ^ 2) / (2 + 8 * lam ^ 2 * t ^ 2) := by
  have hlin : linCoeff a t ^ 2 = -(((t * a) ^ 2 : ℝ) : ℂ) := by
    simp only [linCoeff, mul_pow, Complex.I_sq]
    push_cast
    ring
  have hre : ((((t : ℂ) * (a : ℂ)) ^ 2).re) = t ^ 2 * a ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    ring
  have him : ((((t : ℂ) * (a : ℂ)) ^ 2).im) = 0 := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hqim : (quadCoeff lam t).im = t * lam := by
    simp only [quadCoeff, Complex.add_im, Complex.div_im, Complex.neg_im,
      Complex.ofReal_im, Complex.ofReal_re, re_ofNat, im_ofNat, normSq_ofNat,
      Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hqnorm : Complex.normSq (quadCoeff lam t) = 1 / 4 + (t * lam) ^ 2 := by
    rw [Complex.normSq_apply, quadCoeff_re, hqim]
    ring
  rw [Complex.neg_re, hlin, Complex.div_re]
  simp only [ofReal_pow, ofReal_mul, neg_re, mul_re, re_ofNat, im_ofNat,
    zero_mul, sub_zero, neg_mul, map_mul, normSq_ofNat, neg_im, mul_im, add_zero,
    neg_add_rev]
  rw [hre, him, quadCoeff_re, hqnorm]
  have hpos : 0 < 4 + 16 * (t * lam) ^ 2 := by positivity
  field_simp [hpos.ne']
  ring

/-- A norm identity for the factor, in a form directly matching Mathlib's
principal complex square root.  The next theorem simplifies the real
prefactor to the fourth root appearing in KSSS (4.28). -/
theorem coordinate_charFactor_norm_raw (a lam t : ℝ) :
    ‖∫ x : ℝ, cexp ((((t * coordinatePolynomial a lam x : ℝ) : ℂ) * I))
        ∂standardGaussian‖
      = (√(2 * π))⁻¹ *
          (π / √(1 / 4 + (t * lam) ^ 2)) ^ (1 / 2 : ℝ) *
            rexp (-(a ^ 2 * t ^ 2) / (2 + 8 * lam ^ 2 * t ^ 2)) := by
  rw [coordinate_charFactor_complex, norm_mul, norm_mul, Complex.norm_exp,
    quadraticExponent_re]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_real]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2
    (mul_pos (by norm_num) Real.pi_pos)), norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, norm_neg, norm_quadCoeff]

private lemma two_mul_sqrt_quarter_add_sq (u : ℝ) :
    2 * √(1 / 4 + u ^ 2) = √(1 + 4 * u ^ 2) := by
  have h : 1 / 4 + u ^ 2 = (1 + 4 * u ^ 2) / 4 := by ring
  rw [h, Real.sqrt_div (by positivity)]
  have hsqrt4 : √(4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [hsqrt4]
  ring

private lemma gaussian_prefactor_eq (u : ℝ) :
    (√(2 * π))⁻¹ * (π / √(1 / 4 + u ^ 2)) ^ (1 / 2 : ℝ) =
      (√(√(1 + 4 * u ^ 2)))⁻¹ := by
  rw [← Real.sqrt_eq_rpow]
  have hx : 0 < 1 + 4 * u ^ 2 := by positivity
  have hq : 0 < 1 / 4 + u ^ 2 := by positivity
  have hy : 0 ≤ π / √(1 / 4 + u ^ 2) := by positivity
  have hleft : 0 ≤ (√(2 * π))⁻¹ * √(π / √(1 / 4 + u ^ 2)) := by positivity
  have hright : 0 ≤ (√(√(1 + 4 * u ^ 2)))⁻¹ := by positivity
  rw [← sq_eq_sq₀ hleft hright, mul_pow, inv_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * π), Real.sq_sqrt hy,
    inv_pow,
    Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hscale := two_mul_sqrt_quarter_add_sq u
  rw [← hscale]
  field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hq).ne',
    (Real.sqrt_pos.2 hx).ne']

private lemma sqrt_sqrt_eq_fourth_rpow (x : ℝ) (hx : 0 ≤ x) :
    √(√x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

/-- KSSS equation (4.28): the exact modulus of the characteristic function
of `a W + lam W²` for a standard Gaussian `W`. -/
theorem coordinate_charFactor_norm (a lam t : ℝ) :
    ‖∫ x : ℝ, cexp ((((t * coordinatePolynomial a lam x : ℝ) : ℂ) * I))
        ∂standardGaussian‖
      = rexp (-(a ^ 2 * t ^ 2) / (2 + 8 * lam ^ 2 * t ^ 2)) /
          (1 + 4 * lam ^ 2 * t ^ 2) ^ (1 / 4 : ℝ) := by
  rw [coordinate_charFactor_norm_raw, gaussian_prefactor_eq (t * lam)]
  rw [sqrt_sqrt_eq_fourth_rpow _ (by positivity)]
  ring_nf

/-! ## Variance bookkeeping -/

/-- The exact pointwise square expansion used to compute the variance of a
centered Gaussian coordinate. -/
lemma centeredCoordinatePolynomial_sq (a lam x : ℝ) :
    centeredCoordinatePolynomial a lam x ^ 2 =
      a ^ 2 * x ^ 2 + 2 * a * lam * x ^ 3 - 2 * a * lam * x +
        lam ^ 2 * x ^ 4 - 2 * lam ^ 2 * x ^ 2 + lam ^ 2 := by
  simp only [centeredCoordinatePolynomial]
  ring

/-- The variance contribution of `a W + lam (W² - 1)`, namely
`a² + 2 lam²`. -/
def coordinateVariance (a lam : ℝ) : ℝ := a ^ 2 + 2 * lam ^ 2

lemma coordinateVariance_nonneg (a lam : ℝ) : 0 ≤ coordinateVariance a lam := by
  simp only [coordinateVariance]
  positivity

lemma coordinateVariance_eq_zero_iff (a lam : ℝ) :
    coordinateVariance a lam = 0 ↔ a = 0 ∧ lam = 0 := by
  simp only [coordinateVariance]
  constructor
  · intro h
    have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg lam]
    have hlam : lam ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg lam]
    exact ⟨sq_eq_zero_iff.mp ha, sq_eq_zero_iff.mp hlam⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- Algebraic extraction of the Gaussian variance from the first four
standard moments.  The hypotheses are stated as values of an arbitrary
linear expectation functional, so the lemma can be reused both for integrals
and for finite approximations. -/
theorem coordinateVariance_of_standardMoments
    (E : ℝ[X] →ₗ[ℝ] ℝ)
    (h0 : E 1 = 1) (h1 : E Polynomial.X = 0)
    (h2 : E (Polynomial.X ^ 2) = 1)
    (h3 : E (Polynomial.X ^ 3) = 0)
    (h4 : E (Polynomial.X ^ 4) = 3) (a lam : ℝ) :
    E ((Polynomial.C a * Polynomial.X +
        Polynomial.C lam * (Polynomial.X ^ 2 - 1)) ^ 2) =
      coordinateVariance a lam := by
  rw [show (Polynomial.C a * Polynomial.X +
      Polynomial.C lam * (Polynomial.X ^ 2 - 1)) ^ 2 =
      Polynomial.C (a ^ 2) * Polynomial.X ^ 2 +
      Polynomial.C (2 * a * lam) * Polynomial.X ^ 3 -
        Polynomial.C (2 * a * lam) * Polynomial.X +
        Polynomial.C (lam ^ 2) * Polynomial.X ^ 4 -
        Polynomial.C (2 * lam ^ 2) * Polynomial.X ^ 2 +
        Polynomial.C (lam ^ 2) * 1 by
      simp only [Polynomial.C_pow, Polynomial.C_mul, map_ofNat]
      ring]
  have hC (c : ℝ) (p : ℝ[X]) : E (Polynomial.C c * p) = c * E p := by
    rw [Polynomial.C_mul', map_smul]
    rfl
  simp only [map_add, map_sub, hC, h0, h1, h2, h3, h4, coordinateVariance]
  ring

/-- Total variance of independent diagonal Gaussian factors. -/
def totalVariance {ι : Type*} [Fintype ι] (a lam : ι → ℝ) : ℝ :=
  ∑ i, coordinateVariance (a i) (lam i)

lemma totalVariance_nonneg {ι : Type*} [Fintype ι] (a lam : ι → ℝ) :
    0 ≤ totalVariance a lam := by
  exact Finset.sum_nonneg fun i _ ↦ coordinateVariance_nonneg (a i) (lam i)

/-- The standard deviation of one centered diagonal coordinate. -/
noncomputable def coordinateSigma (a lam : ℝ) : ℝ :=
  √(coordinateVariance a lam)

lemma coordinateSigma_nonneg (a lam : ℝ) : 0 ≤ coordinateSigma a lam :=
  Real.sqrt_nonneg _

lemma coordinateSigma_sq (a lam : ℝ) :
    coordinateSigma a lam ^ 2 = coordinateVariance a lam := by
  exact Real.sq_sqrt (coordinateVariance_nonneg a lam)

/-- The standard deviation of the full independent diagonal sum. -/
noncomputable def diagonalSigma {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) : ℝ :=
  √(totalVariance a lam)

/-- The denominator `∑ σᵢ³` in the KSSS Lyapunov parameter. -/
noncomputable def sigmaCubeSum {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) : ℝ :=
  ∑ i, coordinateSigma (a i) (lam i) ^ 3

/-- The exact third absolute moment of one centered coordinate. -/
noncomputable def coordinateThirdAbsMoment (a lam : ℝ) : ℝ :=
  ∫ x : ℝ, |centeredCoordinatePolynomial a lam x| ^ 3 ∂standardGaussian

/-- Sum of the coordinate third absolute moments. -/
noncomputable def totalThirdAbsMoment {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) : ℝ :=
  ∑ i, coordinateThirdAbsMoment (a i) (lam i)

/-- KSSS's parameter `Γ = σ³ / ∑ σᵢ³`. -/
noncomputable def lyapunovGamma {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) : ℝ :=
  diagonalSigma a lam ^ 3 / sigmaCubeSum a lam

/-- The normalized third-moment parameter used by the standard local CLT. -/
noncomputable def lyapunovL {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) : ℝ :=
  totalThirdAbsMoment a lam / diagonalSigma a lam ^ 3

lemma diagonalSigma_eq_one_of_totalVariance_eq_one
    {ι : Type*} [Fintype ι] {a lam : ι → ℝ}
    (hsum : totalVariance a lam = 1) : diagonalSigma a lam = 1 := by
  simp [diagonalSigma, hsum]

lemma lyapunovGamma_eq_inv_sigmaCubeSum_of_normalized
    {ι : Type*} [Fintype ι] {a lam : ι → ℝ}
    (hsum : totalVariance a lam = 1) :
    lyapunovGamma a lam = (sigmaCubeSum a lam)⁻¹ := by
  rw [lyapunovGamma, diagonalSigma_eq_one_of_totalVariance_eq_one hsum]
  simp

lemma lyapunovL_eq_totalThirdAbsMoment_of_normalized
    {ι : Type*} [Fintype ι] {a lam : ι → ℝ}
    (hsum : totalVariance a lam = 1) :
    lyapunovL a lam = totalThirdAbsMoment a lam := by
  rw [lyapunovL, diagonalSigma_eq_one_of_totalVariance_eq_one hsum]
  simp

/-- The parameter comparison in the proof of KSSS Lemma 5.5(a).  KSSS
obtains the coordinate hypotheses from Hölder and degree-two Gaussian
hypercontractivity: `σᵢ³ ≤ E|Xᵢ|³ ≤ 8σᵢ³`. -/
theorem lyapunov_parameter_bounds_of_coordinate_moments
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    (hsum : totalVariance a lam = 1)
    (hlower : ∀ i, coordinateSigma (a i) (lam i) ^ 3 ≤
      coordinateThirdAbsMoment (a i) (lam i))
    (hupper : ∀ i, coordinateThirdAbsMoment (a i) (lam i) ≤
      8 * coordinateSigma (a i) (lam i) ^ 3) :
    1 / lyapunovGamma a lam ≤ lyapunovL a lam ∧
      lyapunovL a lam ≤ 8 / lyapunovGamma a lam := by
  have hlowerSum : sigmaCubeSum a lam ≤ totalThirdAbsMoment a lam := by
    unfold sigmaCubeSum totalThirdAbsMoment
    exact Finset.sum_le_sum fun i hi ↦ hlower i
  have hupperSum : totalThirdAbsMoment a lam ≤ 8 * sigmaCubeSum a lam := by
    unfold sigmaCubeSum totalThirdAbsMoment
    calc
      ∑ i, coordinateThirdAbsMoment (a i) (lam i) ≤
          ∑ i, 8 * coordinateSigma (a i) (lam i) ^ 3 :=
        Finset.sum_le_sum fun i hi ↦ hupper i
      _ = 8 * ∑ i, coordinateSigma (a i) (lam i) ^ 3 := by
        rw [Finset.mul_sum]
  rw [lyapunovGamma_eq_inv_sigmaCubeSum_of_normalized hsum,
    lyapunovL_eq_totalThirdAbsMoment_of_normalized hsum]
  constructor
  · simpa [div_eq_mul_inv] using hlowerSum
  · simpa [div_eq_mul_inv] using hupperSum

lemma sigmaCubeSum_pos_of_totalVariance_eq_one
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    (hsum : totalVariance a lam = 1) : 0 < sigmaCubeSum a lam := by
  classical
  have htv : 0 < totalVariance a lam := by
    rw [hsum]
    norm_num
  have hvarSum : 0 < ∑ i, coordinateVariance (a i) (lam i) := by
    simpa only [totalVariance] using htv
  have hex : ∃ i, 0 < coordinateVariance (a i) (lam i) := by
    have h := (Finset.sum_pos_iff_of_nonneg
      (s := Finset.univ)
      (fun i _ ↦ coordinateVariance_nonneg (a i) (lam i))).mp hvarSum
    simpa using h
  obtain ⟨i, hi⟩ := hex
  have hsigma : 0 < coordinateSigma (a i) (lam i) :=
    Real.sqrt_pos.2 hi
  have hterm : 0 < coordinateSigma (a i) (lam i) ^ 3 := pow_pos hsigma 3
  have hle : coordinateSigma (a i) (lam i) ^ 3 ≤ sigmaCubeSum a lam := by
    unfold sigmaCubeSum
    exact Finset.single_le_sum
      (fun j _ ↦ pow_nonneg (coordinateSigma_nonneg (a j) (lam j)) 3)
      (Finset.mem_univ i)
  exact hterm.trans_le hle

lemma lyapunovGamma_pos_of_totalVariance_eq_one
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    (hsum : totalVariance a lam = 1) : 0 < lyapunovGamma a lam := by
  rw [lyapunovGamma_eq_inv_sigmaCubeSum_of_normalized hsum]
  exact inv_pos.mpr (sigmaCubeSum_pos_of_totalVariance_eq_one a lam hsum)

lemma lyapunovL_pos_of_coordinate_moments
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    (hsum : totalVariance a lam = 1)
    (hlower : ∀ i, coordinateSigma (a i) (lam i) ^ 3 ≤
      coordinateThirdAbsMoment (a i) (lam i))
    (hupper : ∀ i, coordinateThirdAbsMoment (a i) (lam i) ≤
      8 * coordinateSigma (a i) (lam i) ^ 3) :
    0 < lyapunovL a lam := by
  have hGamma := lyapunovGamma_pos_of_totalVariance_eq_one a lam hsum
  have hbounds := lyapunov_parameter_bounds_of_coordinate_moments
    a lam hsum hlower hupper
  exact (one_div_pos.mpr hGamma).trans_le hbounds.1

/-
The following estimate is the one-coordinate analytic core of KSSS
Lemma 5.5(b).  After normalizing the total variance to one, `w` is the
variance of the coordinate under consideration.  The hypothesis `w ≤ 1/4`
is exactly the no-influential-coordinate hypothesis in that lemma.  The
left side is what remains after raising the characteristic modulus to the
Hölder exponent `1 / w` and applying Bernoulli's inequality to its quadratic
factor.
-/
theorem holderCoordinateDecay_le (a lam w t : ℝ)
    (hw : w = coordinateVariance a lam) (hwpos : 0 < w) (hwle : w ≤ 1 / 4) :
    rexp (-(a ^ 2 * t ^ 2) / ((2 + 8 * lam ^ 2 * t ^ 2) * w)) /
        (1 + lam ^ 2 * t ^ 2 / w) ≤
      (1 + t ^ 2 / 2)⁻¹ := by
  let A := a ^ 2 * t ^ 2 / ((2 + 8 * lam ^ 2 * t ^ 2) * w)
  let B := lam ^ 2 * t ^ 2 / w
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hden : 2 + 8 * lam ^ 2 * t ^ 2 ≤ 2 * (1 + B) := by
    dsimp [B]
    have h4w : 4 * w ≤ 1 := by linarith
    field_simp [hwpos.ne']
    nlinarith [sq_nonneg lam, sq_nonneg t,
      mul_nonneg (sq_nonneg lam) (sq_nonneg t)]
  have hA_lower :
      a ^ 2 * t ^ 2 / (2 * w * (1 + B)) ≤ A := by
    dsimp [A]
    apply div_le_div_of_nonneg_left
    · positivity
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_right hden hwpos.le]
  have hA_lower_mul : a ^ 2 * t ^ 2 / (2 * w) ≤ A * (1 + B) := by
    calc
      a ^ 2 * t ^ 2 / (2 * w) =
          (a ^ 2 * t ^ 2 / (2 * w * (1 + B))) * (1 + B) := by
            field_simp [hwpos.ne', show 1 + B ≠ 0 by positivity]
      _ ≤ A * (1 + B) := mul_le_mul_of_nonneg_right hA_lower (by positivity)
  have hvariance : a ^ 2 + 2 * lam ^ 2 = w := by
    simpa only [coordinateVariance] using hw.symm
  have hprod : 1 + t ^ 2 / 2 ≤ (1 + A) * (1 + B) := by
    calc
      1 + t ^ 2 / 2 = 1 + B + a ^ 2 * t ^ 2 / (2 * w) := by
        dsimp [B]
        field_simp [hwpos.ne']
        nlinarith
      _ ≤ 1 + B + A * (1 + B) := by
        simpa [add_comm] using add_le_add_left hA_lower_mul (1 + B)
      _ = (1 + A) * (1 + B) := by ring
  have hexp : rexp (-A) ≤ (1 + A)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos A) (by positivity)).2
      (by simpa only [add_comm] using Real.add_one_le_exp A)
  have hmain : rexp (-A) / (1 + B) ≤ (1 + t ^ 2 / 2)⁻¹ := by
    calc
      rexp (-A) / (1 + B) ≤ (1 + A)⁻¹ / (1 + B) :=
        div_le_div_of_nonneg_right hexp (by positivity)
      _ = ((1 + A) * (1 + B))⁻¹ := by
        field_simp [show 1 + A ≠ 0 by positivity, show 1 + B ≠ 0 by positivity]
      _ ≤ (1 + t ^ 2 / 2)⁻¹ :=
        (inv_le_inv₀ (by positivity) (by positivity)).2 hprod
  simpa only [A, B, neg_div] using hmain

/-- The actual characteristic-function form of the one-coordinate estimate
used in KSSS Lemma 5.5(b).  The outer real power is the weighted Hölder
exponent. -/
theorem coordinateCharFactor_holderPower_le (a lam w t : ℝ)
    (hw : w = coordinateVariance a lam) (hwpos : 0 < w) (hwle : w ≤ 1 / 4) :
    ‖∫ x : ℝ, cexp ((((t * coordinatePolynomial a lam x : ℝ) : ℂ) * I))
        ∂standardGaussian‖ ^ (1 / w : ℝ) ≤
      (1 + t ^ 2 / 2)⁻¹ := by
  rw [coordinate_charFactor_norm]
  let E := -(a ^ 2 * t ^ 2) / (2 + 8 * lam ^ 2 * t ^ 2)
  let Q := 1 + 4 * lam ^ 2 * t ^ 2
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hnum : rexp E ^ (1 / w : ℝ) =
      rexp (-(a ^ 2 * t ^ 2) / ((2 + 8 * lam ^ 2 * t ^ 2) * w)) := by
    rw [← Real.exp_mul]
    congr 1
    dsimp [E]
    field_simp [hwpos.ne']
  have hdenpow : (Q ^ (1 / 4 : ℝ)) ^ (1 / w : ℝ) =
      Q ^ (1 / (4 * w) : ℝ) := by
    rw [← Real.rpow_mul hQ]
    congr 1
    field_simp [hwpos.ne']
  have hp : 1 ≤ 1 / (4 * w) := by
    rw [le_div_iff₀ (by positivity : 0 < 4 * w)]
    linarith
  have hs : -1 ≤ 4 * lam ^ 2 * t ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg lam) (sq_nonneg t)]
  have hbern := one_add_mul_self_le_rpow_one_add (s := 4 * lam ^ 2 * t ^ 2) hs hp
  have hden : 1 + lam ^ 2 * t ^ 2 / w ≤ Q ^ (1 / (4 * w) : ℝ) := by
    calc
      1 + lam ^ 2 * t ^ 2 / w =
          1 + (1 / (4 * w)) * (4 * lam ^ 2 * t ^ 2) := by
            field_simp [hwpos.ne']
      _ ≤ (1 + 4 * lam ^ 2 * t ^ 2) ^ (1 / (4 * w) : ℝ) := hbern
      _ = Q ^ (1 / (4 * w) : ℝ) := by rfl
  have hsplit :
      (rexp E / Q ^ (1 / 4 : ℝ)) ^ (1 / w : ℝ) =
        rexp (-(a ^ 2 * t ^ 2) / ((2 + 8 * lam ^ 2 * t ^ 2) * w)) /
          Q ^ (1 / (4 * w) : ℝ) := by
    rw [Real.div_rpow (Real.exp_pos E).le (Real.rpow_nonneg hQ _) _, hnum, hdenpow]
  change (rexp E / Q ^ (1 / 4 : ℝ)) ^ (1 / w : ℝ) ≤ _
  rw [hsplit]
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans
    (holderCoordinateDecay_le a lam w t hw hwpos hwle)

/-- The universal integrable envelope appearing after the one-coordinate
Hölder estimate in KSSS Lemma 5.5(b). -/
noncomputable def holderEnvelope (t : ℝ) : ℝ := (1 + t ^ 2 / 2)⁻¹

/-- The one-coordinate estimate in the form used by the finite product.
Unlike `coordinateCharFactor_holderPower_le`, this statement also covers a
zero-variance coordinate, whose characteristic factor is identically one. -/
theorem coordinateCharFactor_le_holderEnvelope_rpow (a lam t : ℝ)
    (hsmall : coordinateVariance a lam ≤ 1 / 4) :
    ‖∫ x : ℝ, cexp ((((t * coordinatePolynomial a lam x : ℝ) : ℂ) * I))
        ∂standardGaussian‖ ≤ holderEnvelope t ^ coordinateVariance a lam := by
  rcases eq_or_lt_of_le (coordinateVariance_nonneg a lam) with hzero | hpos
  · have hvzero : coordinateVariance a lam = 0 := hzero.symm
    obtain ⟨ha, hlam⟩ := (coordinateVariance_eq_zero_iff a lam).mp hvzero
    subst a
    subst lam
    rw [coordinate_charFactor_norm]
    simp [coordinateVariance, holderEnvelope]
  · have hi := coordinateCharFactor_holderPower_le
      a lam (coordinateVariance a lam) t rfl hpos hsmall
    have hp := Real.rpow_le_rpow
      (Real.rpow_nonneg (norm_nonneg _) _) hi hpos.le
    simpa only [holderEnvelope, one_div,
      Real.rpow_inv_rpow (norm_nonneg _) hpos.ne'] using hp

lemma holderEnvelope_continuous : Continuous holderEnvelope := by
  unfold holderEnvelope
  apply Continuous.inv₀
  · fun_prop
  · intro t
    positivity

lemma holderEnvelope_nonneg (t : ℝ) : 0 ≤ holderEnvelope t := by
  unfold holderEnvelope
  positivity

lemma holderEnvelope_even (t : ℝ) : holderEnvelope (-t) = holderEnvelope t := by
  unfold holderEnvelope
  congr 1
  ring

lemma holderEnvelope_integrable : Integrable holderEnvelope := by
  have hsqrt : √(2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have h := integrable_inv_one_add_sq.comp_div hsqrt
  refine h.congr (Filter.Eventually.of_forall fun t ↦ ?_)
  unfold holderEnvelope
  congr 1
  field_simp [hsqrt]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Positive-half-line integration of the KSSS Lemma 5.5(b) envelope.
The companion negative-half-line estimate is obtained by the evenness of
`holderEnvelope`. -/
theorem holderEnvelope_integral_Ioi_le {K : ℝ} (hK : 0 < K) :
    ∫ t : ℝ in Set.Ioi K, holderEnvelope t ≤ 2 / K := by
  have hg : IntegrableOn (fun t : ℝ ↦ 2 * t ^ (-2 : ℝ)) (Set.Ioi K) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hK).const_mul 2
  have hpoint : ∀ t ∈ Set.Ioi K, holderEnvelope t ≤ 2 * t ^ (-2 : ℝ) := by
    intro t ht
    have htpos : 0 < t := hK.trans ht
    rw [Real.rpow_neg_ofNat]
    unfold holderEnvelope
    field_simp [htpos.ne']
    nlinarith [sq_pos_of_pos htpos]
  have hf : IntegrableOn holderEnvelope (Set.Ioi K) := by
    refine hg.mono_nonneg holderEnvelope_continuous.aestronglyMeasurable ?_ ?_
    · exact Filter.Eventually.of_forall holderEnvelope_nonneg
    · exact (ae_restrict_mem measurableSet_Ioi).mono hpoint
  calc
    ∫ t : ℝ in Set.Ioi K, holderEnvelope t ≤
        ∫ t : ℝ in Set.Ioi K, 2 * t ^ (-2 : ℝ) :=
      setIntegral_mono_on hf hg measurableSet_Ioi hpoint
    _ = 2 / K := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hK]
      norm_num [Real.rpow_neg_natCast, zpow_neg, hK.ne']
      simpa only [Real.rpow_neg_one, div_eq_mul_inv]

/-- The two-sided universal tail integral used in KSSS Lemma 5.5(b). -/
theorem holderEnvelope_integral_twoSided_le {K : ℝ} (hK : 0 < K) :
    ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K, holderEnvelope t ≤ 4 / K := by
  have hdisj : Disjoint (Set.Iic (-K)) (Set.Ioi K) := by
    rw [Set.disjoint_left]
    intro t htneg htpos
    change t ≤ -K at htneg
    change K < t at htpos
    linarith
  have hneg :
      ∫ t : ℝ in Set.Iic (-K), holderEnvelope t =
        ∫ t : ℝ in Set.Ioi K, holderEnvelope t := by
    simpa only [neg_neg, holderEnvelope_even] using
      (integral_comp_neg_Iic (-K) holderEnvelope)
  have htail := holderEnvelope_integral_Ioi_le hK
  rw [setIntegral_union hdisj measurableSet_Ioi
    (holderEnvelope_integrable.integrableOn) (holderEnvelope_integrable.integrableOn), hneg]
  calc
    _ ≤ 2 / K + 2 / K := add_le_add htail htail
    _ = 4 / K := by ring

/-! ## The density-comparison interface in KSSS Lemma 5.5(a) -/

/-- The characteristic function of the normalized comparison Gaussian. -/
noncomputable def standardNormalChar (t : ℝ) : ℂ :=
  (rexp (-t ^ 2 / 2) : ℂ)

/-- The density of the normalized comparison Gaussian. -/
noncomputable def standardNormalDensity (u : ℝ) : ℝ :=
  rexp (-u ^ 2 / 2) / √(2 * π)

/-- The exact Fourier-inversion identity needed to compare two continuous
densities.  It is separated out because Mathlib currently supplies Fourier
inversion for integrable functions, but not the probability-theoretic theorem
that an arbitrary law with integrable characteristic function has a density. -/
def HasFourierDensityDifference (p q : ℝ → ℝ) (phi psi : ℝ → ℂ) : Prop :=
  ∀ u : ℝ,
    (((p u - q u : ℝ) : ℂ)) =
      (((2 * π : ℝ) : ℂ))⁻¹ *
        ∫ t : ℝ, (phi t - psi t) *
          cexp (-(((t * u : ℝ) : ℂ) * I))

/-- An individual inverse-Fourier representation of a density, with the
KSSS normalization `1/(2π)`. -/
def HasInverseFourierDensity (p : ℝ → ℝ) (phi : ℝ → ℂ) : Prop :=
  ∀ u : ℝ,
    ((p u : ℝ) : ℂ) =
      (((2 * π : ℝ) : ℂ))⁻¹ *
        ∫ t : ℝ, phi t * cexp (-(((t * u : ℝ) : ℂ) * I))

/-- Subtracting two inverse-Fourier representations gives the exact
difference identity consumed by the density-comparison estimate. -/
theorem HasInverseFourierDensity.hasDifference
    {p q : ℝ → ℝ} {phi psi : ℝ → ℂ}
    (hp : HasInverseFourierDensity p phi)
    (hq : HasInverseFourierDensity q psi)
    (hphi : Integrable phi) (hpsi : Integrable psi) :
    HasFourierDensityDifference p q phi psi := by
  intro u
  let phase : ℝ → ℂ := fun t ↦ cexp (-(((t * u : ℝ) : ℂ) * I))
  have hphase : AEStronglyMeasurable phase := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hphaseBound : ∀ᵐ t : ℝ, ‖phase t‖ ≤ 1 := by
    exact Filter.Eventually.of_forall fun t ↦ by
      dsimp [phase]
      rw [Complex.norm_exp]
      simp
  have hphiPhase : Integrable (fun t : ℝ ↦ phi t * phase t) :=
    hphi.mul_bdd hphase hphaseBound
  have hpsiPhase : Integrable (fun t : ℝ ↦ psi t * phase t) :=
    hpsi.mul_bdd hphase hphaseBound
  rw [Complex.ofReal_sub, hp u, hq u]
  rw [← mul_sub, ← integral_sub hphiPhase hpsiPhase]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    dsimp [phase]
    ring

lemma standardNormalChar_integrable : Integrable standardNormalChar := by
  have hreal : Integrable (fun t : ℝ ↦ rexp (-(1 / 2 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hcomplex : Integrable (fun t : ℝ ↦ (rexp (-(1 / 2 : ℝ) * t ^ 2) : ℂ)) :=
    hreal.ofReal
  refine hcomplex.congr (Filter.Eventually.of_forall fun t ↦ ?_)
  unfold standardNormalChar
  congr 1
  ring_nf

lemma norm_standardNormalChar (t : ℝ) :
    ‖standardNormalChar t‖ = rexp (-t ^ 2 / 2) := by
  rw [standardNormalChar, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- Fourier inversion converts an `L¹` characteristic-function estimate
directly into a uniform density estimate.  The normalization is the one used
in KSSS equation (4.1). -/
theorem abs_density_sub_le_integral_norm_char_sub
    {p q : ℝ → ℝ} {phi psi : ℝ → ℂ}
    (hInv : HasFourierDensityDifference p q phi psi) (u : ℝ) :
    |p u - q u| ≤ (2 * π)⁻¹ * ∫ t : ℝ, ‖phi t - psi t‖ := by
  have hphase (t : ℝ) :
      ‖(phi t - psi t) * cexp (-(((t * u : ℝ) : ℂ) * I))‖ =
        ‖phi t - psi t‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hInv u, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖∫ t : ℝ, (phi t - psi t) * cexp (-(((t * u : ℝ) : ℂ) * I))‖ ≤
        ∫ t : ℝ, ‖(phi t - psi t) * cexp (-(((t * u : ℝ) : ℂ) * I))‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, ‖phi t - psi t‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hphase

lemma standardNormalChar_norm_le_holderEnvelope (t : ℝ) :
    ‖standardNormalChar t‖ ≤ holderEnvelope t := by
  rw [norm_standardNormalChar]
  unfold holderEnvelope
  rw [show -t ^ 2 / 2 = -(t ^ 2 / 2) by ring]
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos (t ^ 2 / 2)) (by positivity)).2
    (by simpa only [add_comm] using Real.add_one_le_exp (t ^ 2 / 2))

/-- The normalized Gaussian characteristic function contributes at most
`4 / K` outside `[-K,K]`.  This is the Gaussian-tail term in the proof of
KSSS Lemma 5.5(a). -/
theorem standardNormalChar_integral_twoSided_le {K : ℝ} (hK : 0 < K) :
    ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K, ‖standardNormalChar t‖ ≤ 4 / K := by
  have hnorm : Integrable (fun t : ℝ ↦ ‖standardNormalChar t‖) :=
    standardNormalChar_integrable.norm
  calc
    ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K, ‖standardNormalChar t‖ ≤
        ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K, holderEnvelope t := by
      apply setIntegral_mono_on hnorm.integrableOn holderEnvelope_integrable.integrableOn
        ((measurableSet_Iic.union measurableSet_Ioi))
      intro t ht
      exact standardNormalChar_norm_le_holderEnvelope t
    _ ≤ 4 / K := holderEnvelope_integral_twoSided_le hK

/-- The exact central-plus-tail assembly in KSSS Lemma 5.5(a), normalized to
total variance one.  `central / Gamma` is the standard local-CLT contribution;
`tail` is the remaining characteristic-function tail.  The explicit `128`
comes from integrating the comparison Gaussian outside `Gamma / 32`.

This theorem contains all density/Fourier bookkeeping in Lemma 5.5(a); the
separate local characteristic-function estimate supplies `hcentral`. -/
theorem densityComparison_of_central_and_tail
    {p : ℝ → ℝ} {phi : ℝ → ℂ} {Gamma central tail : ℝ}
    (hGamma : 0 < Gamma)
    (hphi : Integrable phi)
    (hInv : HasFourierDensityDifference
      p standardNormalDensity phi standardNormalChar)
    (hcentral :
      ∫ t : ℝ in Set.Ioc (-(Gamma / 32)) (Gamma / 32),
          ‖phi t - standardNormalChar t‖ ≤ central / Gamma)
    (htail :
      ∫ t : ℝ in Set.Iic (-(Gamma / 32)) ∪ Set.Ioi (Gamma / 32),
          ‖phi t‖ ≤ tail) (u : ℝ) :
    |p u - standardNormalDensity u| ≤
      (2 * π)⁻¹ * ((central + 128) / Gamma + tail) := by
  let cutoff := Gamma / 32
  let centralSet : Set ℝ := Set.Ioc (-cutoff) cutoff
  let tailSet : Set ℝ := Set.Iic (-cutoff) ∪ Set.Ioi cutoff
  have hnormal : Integrable standardNormalChar := standardNormalChar_integrable
  have hdiff : Integrable (fun t : ℝ ↦ ‖phi t - standardNormalChar t‖) :=
    (hphi.sub hnormal).norm
  have hsum : Integrable
      (fun t : ℝ ↦ ‖phi t‖ + ‖standardNormalChar t‖) :=
    hphi.norm.add hnormal.norm
  have htailDiff :
      ∫ t : ℝ in tailSet, ‖phi t - standardNormalChar t‖ ≤ tail + 128 / Gamma := by
    calc
      ∫ t : ℝ in tailSet, ‖phi t - standardNormalChar t‖ ≤
          ∫ t : ℝ in tailSet, (‖phi t‖ + ‖standardNormalChar t‖) := by
        apply setIntegral_mono_on hdiff.integrableOn hsum.integrableOn
          (measurableSet_Iic.union measurableSet_Ioi)
        intro t ht
        exact norm_sub_le (phi t) (standardNormalChar t)
      _ = (∫ t : ℝ in tailSet, ‖phi t‖) +
          ∫ t : ℝ in tailSet, ‖standardNormalChar t‖ := by
        rw [integral_add hphi.norm.integrableOn hnormal.norm.integrableOn]
      _ ≤ tail + 128 / Gamma := by
        apply add_le_add
        · simpa only [tailSet, cutoff] using htail
        · have hg := standardNormalChar_integral_twoSided_le
            (show 0 < cutoff by dsimp [cutoff]; positivity)
          calc
            ∫ t : ℝ in tailSet, ‖standardNormalChar t‖ ≤ 4 / cutoff := by
              simpa only [tailSet] using hg
            _ = 128 / Gamma := by
              dsimp [cutoff]
              field_simp [hGamma.ne']
              norm_num
  have hL1 :
      ∫ t : ℝ, ‖phi t - standardNormalChar t‖ ≤
        (central + 128) / Gamma + tail := by
    rw [← integral_add_compl measurableSet_Ioc hdiff]
    have hcompl : centralSetᶜ = tailSet := by
      simp only [centralSet, tailSet, Set.compl_Ioc]
    rw [hcompl]
    calc
      (∫ t : ℝ in centralSet, ‖phi t - standardNormalChar t‖) +
          ∫ t : ℝ in tailSet, ‖phi t - standardNormalChar t‖ ≤
          central / Gamma + (tail + 128 / Gamma) := by
        apply add_le_add
        · simpa only [centralSet, cutoff] using hcentral
        · exact htailDiff
      _ = (central + 128) / Gamma + tail := by ring
  exact (abs_density_sub_le_integral_norm_char_sub hInv u).trans
    (mul_le_mul_of_nonneg_left hL1 (by positivity))

/-- The cubic Gaussian envelope in the standard characteristic-function
estimate used in proofs of the central limit theorem. -/
noncomputable def localCLTEnvelope (t : ℝ) : ℝ :=
  |t| ^ 3 * rexp (-t ^ 2 / 3)

lemma localCLTEnvelope_nonneg (t : ℝ) : 0 ≤ localCLTEnvelope t := by
  unfold localCLTEnvelope
  positivity

lemma localCLTEnvelope_even (t : ℝ) :
    localCLTEnvelope (-t) = localCLTEnvelope t := by
  unfold localCLTEnvelope
  simp only [abs_neg, neg_sq]

lemma localCLTEnvelope_integrable : Integrable localCLTEnvelope := by
  have h : Integrable
      (fun t : ℝ ↦ t ^ (3 : ℝ) * rexp (-(1 / 3 : ℝ) * t ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq (by norm_num) (by norm_num)
  refine h.norm.congr (Filter.Eventually.of_forall fun t ↦ ?_)
  unfold localCLTEnvelope
  have hp3 : t ^ (3 : ℝ) = t ^ (3 : ℕ) := by
    simpa using Real.rpow_natCast t 3
  change ‖t ^ (3 : ℝ) * rexp (-(1 / 3 : ℝ) * t ^ 2)‖ =
    |t| ^ 3 * rexp (-t ^ 2 / 3)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), hp3, abs_pow]
  congr 1
  ring_nf

/-- Exact integral of the local-CLT envelope:
`∫ |t|³ exp (-t² / 3) dt = 9`. -/
theorem integral_localCLTEnvelope :
    ∫ t : ℝ, localCLTEnvelope t = 9 := by
  have hpos : ∫ t : ℝ in Set.Ioi 0, localCLTEnvelope t = 9 / 2 := by
    have h := _root_.integral_rpow_mul_exp_neg_mul_rpow
      (p := (2 : ℝ)) (q := (3 : ℝ)) (b := (1 / 3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    calc
      ∫ t : ℝ in Set.Ioi 0, localCLTEnvelope t =
          ∫ t : ℝ in Set.Ioi 0,
            t ^ (3 : ℝ) * rexp (-(1 / 3 : ℝ) * t ^ (2 : ℝ)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro t ht
              unfold localCLTEnvelope
              have hp3 : t ^ (3 : ℝ) = t ^ (3 : ℕ) := by
                simpa using Real.rpow_natCast t 3
              have hp2 : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
                simpa using Real.rpow_natCast t 2
              rw [abs_of_pos ht]
              change t ^ (3 : ℕ) * rexp (-t ^ (2 : ℕ) / 3) =
                t ^ (3 : ℝ) * rexp (-(1 / 3 : ℝ) * t ^ (2 : ℝ))
              rw [hp3, hp2]
              ring_nf
      _ = (1 / 3 : ℝ) ^ ((-(3 + 1) / 2 : ℝ)) * (1 / 2 : ℝ) *
          Real.Gamma (((3 + 1) / 2 : ℝ)) := h
      _ = 9 / 2 := by
        norm_num [Real.rpow_neg_natCast, Real.Gamma_nat_eq_factorial]
  have hneg :
      ∫ t : ℝ in Set.Iic 0, localCLTEnvelope t =
        ∫ t : ℝ in Set.Ioi 0, localCLTEnvelope t := by
    simpa only [neg_zero, localCLTEnvelope_even] using
      (integral_comp_neg_Iic (0 : ℝ) localCLTEnvelope)
  rw [← integral_add_compl (s := Set.Ioi 0) measurableSet_Ioi localCLTEnvelope_integrable,
    Set.compl_Ioi, hneg, hpos]
  norm_num

/-- Integrating the classical pointwise local-CLT estimate on the central
band gives the central contribution in KSSS Lemma 5.5(a).  The hypothesis
`hlocal` is precisely the external standard estimate cited by KSSS; all
integration and constants are proved here. -/
theorem centralCharIntegral_le_of_localCLT
    {phi : ℝ → ℂ} {Gamma L : ℝ}
    (hGamma : 0 < Gamma) (hL : 0 ≤ L) (hLle : L ≤ 8 / Gamma)
    (hphi : Integrable phi)
    (hlocal : ∀ t : ℝ, |t| ≤ Gamma / 32 →
      ‖phi t - standardNormalChar t‖ ≤ 16 * L * localCLTEnvelope t) :
    ∫ t : ℝ in Set.Ioc (-(Gamma / 32)) (Gamma / 32),
        ‖phi t - standardNormalChar t‖ ≤ 1152 / Gamma := by
  have hdiff : Integrable (fun t : ℝ ↦ ‖phi t - standardNormalChar t‖) :=
    (hphi.sub standardNormalChar_integrable).norm
  have hscaled : Integrable (fun t : ℝ ↦ 16 * L * localCLTEnvelope t) :=
    localCLTEnvelope_integrable.const_mul (16 * L)
  calc
    ∫ t : ℝ in Set.Ioc (-(Gamma / 32)) (Gamma / 32),
        ‖phi t - standardNormalChar t‖ ≤
        ∫ t : ℝ in Set.Ioc (-(Gamma / 32)) (Gamma / 32),
          16 * L * localCLTEnvelope t := by
      apply setIntegral_mono_on hdiff.integrableOn hscaled.integrableOn measurableSet_Ioc
      intro t ht
      apply hlocal
      exact abs_le.mpr ⟨le_of_lt ht.1, ht.2⟩
    _ ≤ ∫ t : ℝ, 16 * L * localCLTEnvelope t := by
      apply setIntegral_le_integral hscaled
      exact Filter.Eventually.of_forall fun t ↦
        mul_nonneg (mul_nonneg (by norm_num) hL) (localCLTEnvelope_nonneg t)
    _ = 144 * L := by
      rw [integral_const_mul, integral_localCLTEnvelope]
      ring
    _ ≤ 144 * (8 / Gamma) :=
      mul_le_mul_of_nonneg_left hLle (by norm_num)
    _ = 1152 / Gamma := by ring

/-- The standard local-CLT estimate is stated on `|t| ≤ 1 / (4L)`.
The KSSS relation `L ≤ 8 / Gamma` puts the entire band
`|t| ≤ Gamma / 32` inside that domain. -/
theorem localCLT_on_gammaBand_of_standard
    {phi : ℝ → ℂ} {Gamma L : ℝ}
    (hGamma : 0 < Gamma) (hL : 0 < L) (hLle : L ≤ 8 / Gamma)
    (hstandard : ∀ t : ℝ, |t| ≤ 1 / (4 * L) →
      ‖phi t - standardNormalChar t‖ ≤ 16 * L * localCLTEnvelope t) :
    ∀ t : ℝ, |t| ≤ Gamma / 32 →
      ‖phi t - standardNormalChar t‖ ≤ 16 * L * localCLTEnvelope t := by
  have hprod : L * Gamma ≤ 8 := (le_div_iff₀ hGamma).mp hLle
  have hcutoff : Gamma / 32 ≤ 1 / (4 * L) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 32)
      (by positivity : 0 < 4 * L)).2
    nlinarith [hprod]
  intro t ht
  exact hstandard t (ht.trans hcutoff)

/-- Normalized KSSS Lemma 5.5(a), reduced only to its cited standard
pointwise local-CLT estimate and the probability-theoretic inversion identity.
The explicit constant here is `1280 = 1152 + 128`. -/
theorem densityComparison_of_localCLT_and_tail
    {p : ℝ → ℝ} {phi : ℝ → ℂ} {Gamma L tail : ℝ}
    (hGamma : 0 < Gamma) (hL : 0 ≤ L) (hLle : L ≤ 8 / Gamma)
    (hphi : Integrable phi)
    (hInv : HasFourierDensityDifference
      p standardNormalDensity phi standardNormalChar)
    (hlocal : ∀ t : ℝ, |t| ≤ Gamma / 32 →
      ‖phi t - standardNormalChar t‖ ≤ 16 * L * localCLTEnvelope t)
    (htail :
      ∫ t : ℝ in Set.Iic (-(Gamma / 32)) ∪ Set.Ioi (Gamma / 32),
          ‖phi t‖ ≤ tail) (u : ℝ) :
    |p u - standardNormalDensity u| ≤
      (2 * π)⁻¹ * (1280 / Gamma + tail) := by
  have hcentral := centralCharIntegral_le_of_localCLT
    hGamma hL hLle hphi hlocal
  simpa only [show (1152 + 128 : ℝ) = 1280 by norm_num] using
    densityComparison_of_central_and_tail
      hGamma hphi hInv hcentral htail u

/-- The normalized KSSS Lemma 5.5(a) interface with the pointwise local-CLT
estimate on its standard domain `|t| ≤ 1/(4L)`. -/
theorem densityComparison_of_standardLocalCLT_and_tail
    {p : ℝ → ℝ} {phi : ℝ → ℂ} {Gamma L tail : ℝ}
    (hGamma : 0 < Gamma) (hL : 0 < L) (hLle : L ≤ 8 / Gamma)
    (hphi : Integrable phi)
    (hInv : HasFourierDensityDifference
      p standardNormalDensity phi standardNormalChar)
    (hstandard : ∀ t : ℝ, |t| ≤ 1 / (4 * L) →
      ‖phi t - standardNormalChar t‖ ≤ 16 * L * localCLTEnvelope t)
    (htail :
      ∫ t : ℝ in Set.Iic (-(Gamma / 32)) ∪ Set.Ioi (Gamma / 32),
          ‖phi t‖ ≤ tail) (u : ℝ) :
    |p u - standardNormalDensity u| ≤
      (2 * π)⁻¹ * (1280 / Gamma + tail) := by
  exact densityComparison_of_localCLT_and_tail hGamma hL.le hLle hphi hInv
    (localCLT_on_gammaBand_of_standard hGamma hL hLle hstandard) htail u

/-- Variances add for the finite pairwise-independent family used after
diagonalization. -/
theorem variance_finset_sum_of_pairwise_independent
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : ι → Ω → ℝ} {s : Finset ι}
    (hLp : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hIndep : Set.Pairwise (s : Set ι) fun i j ↦ X i ⟂ᵢ[μ] X j) :
    Var[∑ i ∈ s, X i; μ] = ∑ i ∈ s, Var[X i; μ] :=
  IndepFun.variance_sum hLp hIndep

/-! ## Frobenius robust-rank adapters -/

/-- A matrix is at squared Frobenius distance at least `s` from every matrix
of rank at most `r`.  This is the robust-rank hypothesis used in KSSS
Theorems 1.6 and 5.2, without assuming existence of a minimizing matrix. -/
def RobustRankAt {m n : Type*} [Fintype m] [Fintype n]
    (r : ℕ) (s : ℝ) (A : Matrix m n ℝ) : Prop :=
  ∀ B : Matrix m n ℝ, B.rank ≤ r → s ≤ ‖A - B‖ ^ 2

lemma robustRankAt_anti_rank {m n : Type*} [Fintype m] [Fintype n]
    {r q : ℕ} (hqr : q ≤ r) {s : ℝ} {A : Matrix m n ℝ}
    (hA : RobustRankAt r s A) : RobustRankAt q s A := by
  intro B hB
  exact hA B (hB.trans hqr)

lemma robustRankAt_mono_cost {m n : Type*} [Fintype m] [Fintype n]
    {r : ℕ} {s u : ℝ} (hus : u ≤ s) {A : Matrix m n ℝ}
    (hA : RobustRankAt r s A) : RobustRankAt r u A := by
  intro B hB
  exact hus.trans (hA B hB)

/-- Restrict a diagonal approximant to a chosen finite set of coordinates. -/
noncomputable def diagonalRestriction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (S : Finset ι) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i ↦ if i ∈ S then v i else 0

lemma rank_diagonalRestriction_le_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (S : Finset ι) :
    (diagonalRestriction v S).rank ≤ S.card := by
  classical
  rw [diagonalRestriction, Matrix.rank_diagonal]
  let f : {i // (if i ∈ S then v i else 0) ≠ 0} → S := fun i ↦
    ⟨i.1, by
      by_contra hi
      exact i.2 (by simp [hi])⟩
  simpa using Fintype.card_le_of_injective f (fun x y h ↦ by
    apply Subtype.ext
    exact congrArg (fun z : S ↦ (z : ι)) h)

/-- Exact squared Frobenius error of the diagonal truncation.  This is the
constructive (upper-bound) half of the Eckart--Young adapter. -/
lemma frobenius_diagonal_sub_restriction_sq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ι → ℝ) (S : Finset ι) :
    ‖Matrix.diagonal v - diagonalRestriction v S‖ ^ 2 =
      ∑ i with i ∉ S, v i ^ 2 := by
  classical
  have hmat : Matrix.diagonal v - diagonalRestriction v S =
      Matrix.diagonal (fun i ↦ if i ∈ S then 0 else v i) := by
    ext i j
    simp only [diagonalRestriction, Matrix.sub_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [hmat, Matrix.frobenius_norm_diagonal]
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Matrix.diagonal_apply, sq_abs, Finset.sum_filter]

/-- A robust-rank hypothesis forces every diagonal truncation with at most
`r` retained coordinates to have the corresponding spectral tail at least
`s`. -/
theorem robustRankAt_diagonal_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} {s : ℝ} {v : ι → ℝ}
    (hA : RobustRankAt r s (Matrix.diagonal v))
    (S : Finset ι) (hS : S.card ≤ r) :
    s ≤ ∑ i with i ∉ S, v i ^ 2 := by
  rw [← frobenius_diagonal_sub_restriction_sq]
  exact hA (diagonalRestriction v S) ((rank_diagonalRestriction_le_card v S).trans hS)

/-! ## Product characteristic-function tail -/

/-- The exponential linear term in (4.28) can only decrease the modulus. -/
theorem coordinate_charFactor_norm_le (a lam t : ℝ) :
    ‖∫ x : ℝ, cexp ((((t * coordinatePolynomial a lam x : ℝ) : ℂ) * I))
        ∂standardGaussian‖
      ≤ ((1 + 4 * lam ^ 2 * t ^ 2) ^ (1 / 4 : ℝ))⁻¹ := by
  rw [coordinate_charFactor_norm, div_eq_mul_inv]
  calc
    rexp (-(a ^ 2 * t ^ 2) / (2 + 8 * lam ^ 2 * t ^ 2)) *
          ((1 + 4 * lam ^ 2 * t ^ 2) ^ (1 / 4 : ℝ))⁻¹
        ≤ 1 * ((1 + 4 * lam ^ 2 * t ^ 2) ^ (1 / 4 : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right (by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (mul_nonneg (sq_nonneg a) (sq_nonneg t)))
          (by positivity))
        (inv_nonneg.2 (Real.rpow_nonneg (by positivity) _))
    _ = ((1 + 4 * lam ^ 2 * t ^ 2) ^ (1 / 4 : ℝ))⁻¹ := one_mul _

/-- The exact diagonal product of one-coordinate characteristic moduli. -/
noncomputable def diagonalCharModulus {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (t : ℝ) : ℝ :=
  ∏ i, ‖∫ x : ℝ,
    cexp ((((t * coordinatePolynomial (a i) (lam i) x : ℝ) : ℂ) * I))
      ∂standardGaussian‖

/-- Characteristic-function factor for the centered coordinate
`a W + lam (W² - 1)`. -/
noncomputable def centeredCoordinateCharFactor (a lam t : ℝ) : ℂ :=
  ∫ x : ℝ,
    cexp ((((t * centeredCoordinatePolynomial a lam x : ℝ) : ℂ) * I))
      ∂standardGaussian

/-- Centering changes the one-coordinate characteristic function only by a
unit-modulus phase. -/
theorem centeredCoordinateCharFactor_eq_phase_mul (a lam t : ℝ) :
    centeredCoordinateCharFactor a lam t =
      cexp (-(((t * lam : ℝ) : ℂ) * I)) *
        ∫ x : ℝ,
          cexp ((((t * coordinatePolynomial a lam x : ℝ) : ℂ) * I))
            ∂standardGaussian := by
  unfold centeredCoordinateCharFactor
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Complex.exp_add]
  apply congrArg cexp
  simp only [centeredCoordinatePolynomial, coordinatePolynomial]
  push_cast
  ring

lemma norm_centeredCoordinateCharFactor (a lam t : ℝ) :
    ‖centeredCoordinateCharFactor a lam t‖ =
      ‖∫ x : ℝ,
        cexp ((((t * coordinatePolynomial a lam x : ℝ) : ℂ) * I))
          ∂standardGaussian‖ := by
  rw [centeredCoordinateCharFactor_eq_phase_mul, norm_mul, Complex.norm_exp]
  have hre : (-(((t * lam : ℝ) : ℂ) * I)).re = 0 := by simp
  rw [hre, Real.exp_zero, one_mul]

/-- The exact product characteristic function after diagonalization and
centering. -/
noncomputable def diagonalCenteredCharProduct {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (t : ℝ) : ℂ :=
  ∏ i, centeredCoordinateCharFactor (a i) (lam i) t

lemma norm_diagonalCenteredCharProduct {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (t : ℝ) :
    ‖diagonalCenteredCharProduct a lam t‖ = diagonalCharModulus a lam t := by
  classical
  simp only [diagonalCenteredCharProduct, diagonalCharModulus, norm_prod,
    norm_centeredCoordinateCharFactor]

/-- Normalized finite-product form of KSSS Lemma 5.5(b).  Under the
no-influential-coordinate hypothesis, the full characteristic modulus is
pointwise bounded by the universal Hölder envelope. -/
theorem diagonalCharModulus_le_holderEnvelope {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ)
    (hsum : totalVariance a lam = 1)
    (hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 4)
    (t : ℝ) :
    diagonalCharModulus a lam t ≤ holderEnvelope t := by
  classical
  have hcoord (i : ι) :
      ‖∫ x : ℝ,
          cexp ((((t * coordinatePolynomial (a i) (lam i) x : ℝ) : ℂ) * I))
            ∂standardGaussian‖ ≤
        holderEnvelope t ^ coordinateVariance (a i) (lam i) := by
    exact coordinateCharFactor_le_holderEnvelope_rpow (a i) (lam i) t (hsmall i)
  calc
    diagonalCharModulus a lam t ≤
        ∏ i, holderEnvelope t ^ coordinateVariance (a i) (lam i) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact hcoord i
    _ = holderEnvelope t := by
      rw [← Real.rpow_sum_of_nonneg (holderEnvelope_nonneg t)
        (fun i _ ↦ coordinateVariance_nonneg (a i) (lam i))]
      simp only [totalVariance] at hsum
      rw [hsum, Real.rpow_one]

/-- The normalized two-sided characteristic-function tail estimate of KSSS
Lemma 5.5(b), with the explicit universal constant `4`. -/
theorem diagonalCharModulus_lintegral_twoSided_le {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ)
    (hsum : totalVariance a lam = 1)
    (hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 4)
    {K : ℝ} (hK : 0 < K) :
    ∫⁻ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K,
        ENNReal.ofReal (diagonalCharModulus a lam t) ≤ ENNReal.ofReal (4 / K) := by
  let T : Set ℝ := Set.Iic (-K) ∪ Set.Ioi K
  calc
    ∫⁻ t : ℝ in T, ENNReal.ofReal (diagonalCharModulus a lam t) ≤
        ∫⁻ t : ℝ in T, ENNReal.ofReal (holderEnvelope t) := by
      apply lintegral_mono
      intro t
      exact ENNReal.ofReal_le_ofReal
        (diagonalCharModulus_le_holderEnvelope a lam hsum hsmall t)
    _ = ENNReal.ofReal (∫ t : ℝ in T, holderEnvelope t) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal holderEnvelope_integrable.integrableOn
        (Filter.Eventually.of_forall holderEnvelope_nonneg)
    _ ≤ ENNReal.ofReal (4 / K) := by
      apply ENNReal.ofReal_le_ofReal
      exact holderEnvelope_integral_twoSided_le hK

/-- Real-integral form of normalized KSSS Lemma 5.5(b).  Integrability of
the centered product is exactly the hypothesis used by Fourier inversion in
part (a), and its norm is the diagonal modulus. -/
theorem diagonalCharModulus_integral_twoSided_le {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ)
    (hsum : totalVariance a lam = 1)
    (hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 4)
    (hchar : Integrable (diagonalCenteredCharProduct a lam))
    {K : ℝ} (hK : 0 < K) :
    ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K,
        diagonalCharModulus a lam t ≤ 4 / K := by
  have hmod : Integrable (diagonalCharModulus a lam) :=
    hchar.norm.congr (Filter.Eventually.of_forall fun t ↦
      norm_diagonalCenteredCharProduct a lam t)
  calc
    ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K,
        diagonalCharModulus a lam t ≤
        ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K, holderEnvelope t := by
      apply setIntegral_mono_on hmod.integrableOn holderEnvelope_integrable.integrableOn
        (measurableSet_Iic.union measurableSet_Ioi)
      intro t ht
      exact diagonalCharModulus_le_holderEnvelope a lam hsum hsmall t
    _ ≤ 4 / K := holderEnvelope_integral_twoSided_le hK

/-- KSSS Lemma 5.5(a)'s normalized density-comparison conclusion for the
actual centered diagonal Gaussian characteristic product.  The cited
pointwise local-CLT estimate and the inversion identity remain explicit. -/
theorem diagonalDensityComparison_of_standardLocalCLT_and_tail
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    {p : ℝ → ℝ} {Gamma L tail : ℝ}
    (hGamma : 0 < Gamma) (hL : 0 < L) (hLle : L ≤ 8 / Gamma)
    (hchar : Integrable (diagonalCenteredCharProduct a lam))
    (hInv : HasFourierDensityDifference p standardNormalDensity
      (diagonalCenteredCharProduct a lam) standardNormalChar)
    (hstandard : ∀ t : ℝ, |t| ≤ 1 / (4 * L) →
      ‖diagonalCenteredCharProduct a lam t - standardNormalChar t‖ ≤
        16 * L * localCLTEnvelope t)
    (htail :
      ∫ t : ℝ in Set.Iic (-(Gamma / 32)) ∪ Set.Ioi (Gamma / 32),
          diagonalCharModulus a lam t ≤ tail) (u : ℝ) :
    |p u - standardNormalDensity u| ≤
      (2 * π)⁻¹ * (1280 / Gamma + tail) := by
  apply densityComparison_of_standardLocalCLT_and_tail
    hGamma hL hLle hchar hInv hstandard
  simpa only [norm_diagonalCenteredCharProduct] using htail

/-- Source-shaped normalized KSSS Lemma 5.5(a) for the actual centered
diagonal product.  The moment hypotheses are exactly the comparison
`σᵢ³ ≤ E|Xᵢ|³ ≤ 8σᵢ³` used by KSSS; they automatically provide positivity
and `L ≤ 8/Γ`.  Thus only the cited standard pointwise local-CLT estimate and
Fourier inversion remain explicit analytic inputs. -/
theorem diagonalDensityComparison_of_coordinateMoments
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    {p : ℝ → ℝ} {tail : ℝ}
    (hsum : totalVariance a lam = 1)
    (hlower : ∀ i, coordinateSigma (a i) (lam i) ^ 3 ≤
      coordinateThirdAbsMoment (a i) (lam i))
    (hupper : ∀ i, coordinateThirdAbsMoment (a i) (lam i) ≤
      8 * coordinateSigma (a i) (lam i) ^ 3)
    (hchar : Integrable (diagonalCenteredCharProduct a lam))
    (hInv : HasFourierDensityDifference p standardNormalDensity
      (diagonalCenteredCharProduct a lam) standardNormalChar)
    (hstandard : ∀ t : ℝ, |t| ≤ 1 / (4 * lyapunovL a lam) →
      ‖diagonalCenteredCharProduct a lam t - standardNormalChar t‖ ≤
        16 * lyapunovL a lam * localCLTEnvelope t)
    (htail :
      ∫ t : ℝ in
          Set.Iic (-(lyapunovGamma a lam / 32)) ∪
            Set.Ioi (lyapunovGamma a lam / 32),
          diagonalCharModulus a lam t ≤ tail) (u : ℝ) :
    |p u - standardNormalDensity u| ≤
      (2 * π)⁻¹ * (1280 / lyapunovGamma a lam + tail) := by
  have hGamma := lyapunovGamma_pos_of_totalVariance_eq_one a lam hsum
  have hL := lyapunovL_pos_of_coordinate_moments a lam hsum hlower hupper
  have hbounds := lyapunov_parameter_bounds_of_coordinate_moments
    a lam hsum hlower hupper
  exact diagonalDensityComparison_of_standardLocalCLT_and_tail
    a lam hGamma hL hbounds.2 hchar hInv hstandard htail u

/-- Variant of `diagonalDensityComparison_of_coordinateMoments` with the two
ordinary inverse-Fourier density identities as inputs. -/
theorem diagonalDensityComparison_of_coordinateMoments_of_inverseFourier
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    {p : ℝ → ℝ} {tail : ℝ}
    (hsum : totalVariance a lam = 1)
    (hlower : ∀ i, coordinateSigma (a i) (lam i) ^ 3 ≤
      coordinateThirdAbsMoment (a i) (lam i))
    (hupper : ∀ i, coordinateThirdAbsMoment (a i) (lam i) ≤
      8 * coordinateSigma (a i) (lam i) ^ 3)
    (hchar : Integrable (diagonalCenteredCharProduct a lam))
    (hpInv : HasInverseFourierDensity p (diagonalCenteredCharProduct a lam))
    (hnormalInv : HasInverseFourierDensity standardNormalDensity standardNormalChar)
    (hstandard : ∀ t : ℝ, |t| ≤ 1 / (4 * lyapunovL a lam) →
      ‖diagonalCenteredCharProduct a lam t - standardNormalChar t‖ ≤
        16 * lyapunovL a lam * localCLTEnvelope t)
    (htail :
      ∫ t : ℝ in
          Set.Iic (-(lyapunovGamma a lam / 32)) ∪
            Set.Ioi (lyapunovGamma a lam / 32),
          diagonalCharModulus a lam t ≤ tail) (u : ℝ) :
    |p u - standardNormalDensity u| ≤
      (2 * π)⁻¹ * (1280 / lyapunovGamma a lam + tail) := by
  exact diagonalDensityComparison_of_coordinateMoments a lam hsum hlower hupper hchar
    (hpInv.hasDifference hnormalInv hchar standardNormalChar_integrable)
    hstandard htail u

/-- KSSS Lemma 5.11 before the final spectral averaging step: the
characteristic modulus is bounded by the product of its quadratic decays. -/
theorem diagonalCharModulus_le {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (t : ℝ) :
    diagonalCharModulus a lam t ≤
      ∏ i, ((1 + 4 * (lam i) ^ 2 * t ^ 2) ^ (1 / 4 : ℝ))⁻¹ := by
  classical
  apply Finset.prod_le_prod
  · intro i hi
    positivity
  · intro i hi
    exact coordinate_charFactor_norm_le (a i) (lam i) t

/-- The spectral-witness form of KSSS Lemma 5.11.  If a set `S` of
diagonal eigenvalues has squared magnitude at least `s`, then those
coordinates alone force `|S|/4` powers of quadratic decay.  The coordinates
outside `S` can only decrease the characteristic modulus.

The later robust-rank argument in KSSS constructs (and averages over) such
spectral witnesses; this theorem is the exact characteristic-function input
to that argument. -/
theorem diagonalCharModulus_le_of_spectralWitness
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ)
    (S : Finset ι) {s : ℝ} (hs : 0 ≤ s)
    (hlarge : ∀ i ∈ S, s ≤ (lam i) ^ 2) (t : ℝ) :
    diagonalCharModulus a lam t ≤
      (1 + 4 * s * t ^ 2) ^ (-(S.card : ℝ) / 4 : ℝ) := by
  classical
  let f : ι → ℝ := fun i ↦
    ((1 + 4 * (lam i) ^ 2 * t ^ 2) ^ (1 / 4 : ℝ))⁻¹
  let q : ℝ := ((1 + 4 * s * t ^ 2) ^ (1 / 4 : ℝ))⁻¹
  have hf_nonneg (i : ι) : 0 ≤ f i := by
    dsimp [f]
    positivity
  have hf_le_one (i : ι) : f i ≤ 1 := by
    dsimp [f]
    apply (inv_le_one₀ (by positivity)).2
    apply Real.one_le_rpow
    · nlinarith [mul_nonneg hs (sq_nonneg t)]
    · norm_num
  have hf_le_q (i : ι) (hi : i ∈ S) : f i ≤ q := by
    have hbase : 1 + 4 * s * t ^ 2 ≤
        1 + 4 * (lam i) ^ 2 * t ^ 2 := by
      have hmul : 4 * s * t ^ 2 ≤ 4 * (lam i) ^ 2 * t ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hlarge i hi) (by norm_num)) (sq_nonneg t)
      linarith
    have hpow : (1 + 4 * s * t ^ 2) ^ (1 / 4 : ℝ) ≤
        (1 + 4 * (lam i) ^ 2 * t ^ 2) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    dsimp [f, q]
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  have hrestrict : (∏ i, f i) ≤ ∏ i ∈ S, f i := by
    exact Finset.prod_le_prod_of_subset_of_le_one
      (Finset.subset_univ S)
      (fun i hi ↦ hf_nonneg i)
      (fun i hi hnot ↦ hf_le_one i)
  have hcommon : (∏ i ∈ S, f i) ≤ q ^ S.card := by
    calc
      (∏ i ∈ S, f i) ≤ ∏ i ∈ S, q := by
        apply Finset.prod_le_prod
        · intro i hi
          exact hf_nonneg i
        · intro i hi
          exact hf_le_q i hi
      _ = q ^ S.card := by simp
  have hqpow : q ^ S.card =
      (1 + 4 * s * t ^ 2) ^ (-(S.card : ℝ) / 4 : ℝ) := by
    dsimp [q]
    rw [← Real.rpow_neg (by positivity : 0 ≤ 1 + 4 * s * t ^ 2)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : 0 ≤ 1 + 4 * s * t ^ 2)]
    congr 1
    ring
  calc
    diagonalCharModulus a lam t ≤ ∏ i, f i := by
      simpa only [f] using diagonalCharModulus_le a lam t
    _ ≤ ∏ i ∈ S, f i := hrestrict
    _ ≤ q ^ S.card := hcommon
    _ = (1 + 4 * s * t ^ 2) ^ (-(S.card : ℝ) / 4 : ℝ) := hqpow

/-- The elementary product inequality used to turn the squared spectral
mass of a block into one quadratic characteristic-function factor. -/
lemma one_add_sum_le_prod_one_add_of_nonneg
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) :
    1 + ∑ i ∈ S, x i ≤ ∏ i ∈ S, (1 + x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hxi : 0 ≤ x i := hx i (by simp)
      have hxS : ∀ j ∈ S, 0 ≤ x j := by
        intro j hj
        exact hx j (Finset.mem_insert_of_mem hj)
      have hsum : 0 ≤ ∑ j ∈ S, x j := Finset.sum_nonneg hxS
      calc
        1 + (x i + ∑ j ∈ S, x j) ≤
            (1 + x i) * (1 + ∑ j ∈ S, x j) := by
              nlinarith [mul_nonneg hxi hsum]
        _ ≤ (1 + x i) * ∏ j ∈ S, (1 + x j) :=
          mul_le_mul_of_nonneg_left (ih hxS) (by positivity)

/-- Block form of the spectral averaging step in KSSS Lemma 5.11.  A
pairwise-disjoint family of `r` coordinate blocks, each carrying squared
eigenvalue mass at least `s`, forces `r/4` powers of quadratic decay.  This
is the form naturally produced by the residue-class partition of the
ordered spectrum in the proof of that lemma. -/
theorem diagonalCharModulus_le_of_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 ≤ s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2) (t : ℝ) :
    diagonalCharModulus a lam t ≤
      (1 + 4 * s * t ^ 2) ^ (-(Fintype.card κ : ℝ) / 4 : ℝ) := by
  classical
  let f : ι → ℝ := fun i ↦
    ((1 + 4 * (lam i) ^ 2 * t ^ 2) ^ (1 / 4 : ℝ))⁻¹
  let q : ℝ := ((1 + 4 * s * t ^ 2) ^ (1 / 4 : ℝ))⁻¹
  let U : Finset ι := (Finset.univ : Finset κ).biUnion B
  have hf_nonneg (i : ι) : 0 ≤ f i := by
    dsimp [f]
    positivity
  have hf_le_one (i : ι) : f i ≤ 1 := by
    dsimp [f]
    apply (inv_le_one₀ (by positivity)).2
    apply Real.one_le_rpow
    · nlinarith [mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg (lam i)))
        (sq_nonneg t)]
    · norm_num
  have hrestrict : (∏ i, f i) ≤ ∏ i ∈ U, f i := by
    exact Finset.prod_le_prod_of_subset_of_le_one
      (Finset.subset_univ U)
      (fun i hi ↦ hf_nonneg i)
      (fun i hi hnot ↦ hf_le_one i)
  have honeBlock (j : κ) :
      (∏ i ∈ B j, f i) ≤ q := by
    have hscaled : 4 * s * t ^ 2 ≤
        ∑ i ∈ B j, 4 * (lam i) ^ 2 * t ^ 2 := by
      calc
        4 * s * t ^ 2 ≤ 4 * (∑ i ∈ B j, (lam i) ^ 2) * t ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hblock j) (by norm_num)) (sq_nonneg t)
        _ = ∑ i ∈ B j, 4 * (lam i) ^ 2 * t ^ 2 := by
          rw [Finset.mul_sum, Finset.sum_mul]
    have hbase : 1 + 4 * s * t ^ 2 ≤
        ∏ i ∈ B j, (1 + 4 * (lam i) ^ 2 * t ^ 2) := by
      calc
        1 + 4 * s * t ^ 2 ≤
            1 + ∑ i ∈ B j, 4 * (lam i) ^ 2 * t ^ 2 :=
          by simpa [add_comm] using add_le_add_left hscaled 1
        _ ≤ ∏ i ∈ B j, (1 + 4 * (lam i) ^ 2 * t ^ 2) :=
          one_add_sum_le_prod_one_add_of_nonneg
            (B j) (fun i ↦ 4 * (lam i) ^ 2 * t ^ 2) (by
              intro i hi
              positivity)
    have hfactor : (∏ i ∈ B j, f i) =
        (∏ i ∈ B j, (1 + 4 * (lam i) ^ 2 * t ^ 2)) ^ (-1 / 4 : ℝ) := by
      dsimp [f]
      rw [← Real.finsetProd_rpow
        (B j) (fun i ↦ 1 + 4 * (lam i) ^ 2 * t ^ 2)
        (fun i hi ↦ by positivity) (-1 / 4 : ℝ)]
      apply Finset.prod_congr rfl
      intro i hi
      convert (Real.rpow_neg
        (by positivity : 0 ≤ 1 + 4 * (lam i) ^ 2 * t ^ 2) (1 / 4 : ℝ)).symm using 1 <;>
        ring_nf
    rw [hfactor]
    calc
      (∏ i ∈ B j, (1 + 4 * (lam i) ^ 2 * t ^ 2)) ^ (-1 / 4 : ℝ) ≤
          (1 + 4 * s * t ^ 2) ^ (-1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)
      _ = q := by
        dsimp [q]
        convert Real.rpow_neg
          (by positivity : 0 ≤ 1 + 4 * s * t ^ 2) (1 / 4 : ℝ) using 1 <;>
          ring_nf
  have hunion : (∏ i ∈ U, f i) = ∏ j, ∏ i ∈ B j, f i := by
    simpa only [U] using (Finset.prod_biUnion (f := f) hdisj)
  have hblocks : (∏ j, ∏ i ∈ B j, f i) ≤ q ^ Fintype.card κ := by
    calc
      (∏ j, ∏ i ∈ B j, f i) ≤ ∏ j, q := by
        apply Finset.prod_le_prod
        · intro j hj
          exact Finset.prod_nonneg fun i hi ↦ hf_nonneg i
        · intro j hj
          exact honeBlock j
      _ = q ^ Fintype.card κ := by simp
  have hqpow : q ^ Fintype.card κ =
      (1 + 4 * s * t ^ 2) ^ (-(Fintype.card κ : ℝ) / 4 : ℝ) := by
    dsimp [q]
    rw [← Real.rpow_neg (by positivity : 0 ≤ 1 + 4 * s * t ^ 2)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : 0 ≤ 1 + 4 * s * t ^ 2)]
    congr 1
    ring
  calc
    diagonalCharModulus a lam t ≤ ∏ i, f i := by
      simpa only [f] using diagonalCharModulus_le a lam t
    _ ≤ ∏ i ∈ U, f i := hrestrict
    _ = ∏ j, ∏ i ∈ B j, f i := hunion
    _ ≤ q ^ Fintype.card κ := hblocks
    _ = (1 + 4 * s * t ^ 2) ^ (-(Fintype.card κ : ℝ) / 4 : ℝ) := hqpow

end GaussianQuadratic
end Erdos88
