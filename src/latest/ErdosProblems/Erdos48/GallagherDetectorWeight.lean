/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherCutoffEnergy
import ErdosProblems.Erdos48.VariableBandLimitedDetector
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Separating Gallagher's smooth detector weight

This file factors the variable zero detector into unweighted von Mangoldt
partial sums and a smooth logarithmic weight. It bounds the finite Abel
variation by a completely explicit gamma-type sum.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open Complex
open BoundedGaps.Maynard

/-- The smooth logarithmic weight separated from the `Λ(n) / n`
coefficient in Gallagher's cutoff argument. -/
noncomputable def gallagherWeight (eta : ℝ) (k n : ℕ) : ℝ :=
  Real.log n ^ k * (n : ℝ) ^ (-eta)

noncomputable def smoothGallagherWeight (eta : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  Real.log x ^ k * x ^ (-eta)

/-- Exact derivative of the smooth Gallagher weight on the positive axis. -/
theorem hasDerivAt_smoothGallagherWeight
    (eta : ℝ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (smoothGallagherWeight eta k)
      (x ^ (-eta - 1) *
        ((k : ℝ) * Real.log x ^ (k - 1) - eta * Real.log x ^ k)) x := by
  have hlog := (Real.hasDerivAt_log hx.ne').pow k
  have hrpow := Real.hasDerivAt_rpow_const (x := x) (p := -eta)
    (Or.inl hx.ne')
  have h := hlog.mul hrpow
  have hpow : x⁻¹ * x ^ (-eta) = x ^ (-eta - 1) := by
    rw [← Real.rpow_neg_one]
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hcoeff :
      (k : ℝ) * Real.log x ^ (k - 1) * x⁻¹ * x ^ (-eta) +
          Real.log x ^ k * (-eta * x ^ (-eta - 1)) =
        x ^ (-eta - 1) *
          ((k : ℝ) * Real.log x ^ (k - 1) - eta * Real.log x ^ k) := by
    rw [mul_assoc ((k : ℝ) * Real.log x ^ (k - 1)), hpow]
    ring
  simp only [Pi.pow_apply] at h
  rw [hcoeff] at h
  change HasDerivAt (fun y : ℝ ↦ Real.log y ^ k * y ^ (-eta))
    (x ^ (-eta - 1) *
      ((k : ℝ) * Real.log x ^ (k - 1) - eta * Real.log x ^ k)) x
  exact h

/-- The unweighted `Λ(n)/n` coefficient, including the character and
vertical phase, whose partial sums enter Gallagher's mean square. -/
noncomputable def gallagherBaseCoefficient
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) *
    chi n * Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))

/-- Splitting the detector coefficient into `Λ(n)/n` and the smooth
Gallagher weight is exact away from `n = 0`. -/
theorem gallagherBaseCoefficient_mul_weight
    {q n : ℕ} (chi : DirichletCharacter ℂ q) (t eta : ℝ) (k : ℕ)
    (hn : 0 < n) :
    gallagherBaseCoefficient chi t n * (gallagherWeight eta k n : ℂ) =
      (weightedVonMangoldtMajorant eta k n : ℂ) * chi n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrpow :
      (n : ℝ) ^ (-(1 : ℝ)) * (n : ℝ) ^ (-eta) =
        (n : ℝ) ^ (-(1 + eta)) := by
    calc
      (n : ℝ) ^ (-(1 : ℝ)) * (n : ℝ) ^ (-eta) =
          (n : ℝ) ^ (-(1 : ℝ) + -eta) :=
        (Real.rpow_add hnR (-(1 : ℝ)) (-eta)).symm
      _ = (n : ℝ) ^ (-(1 + eta)) := by congr 1 <;> ring
  have hscalar :
      (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ))) *
          gallagherWeight eta k n =
        weightedVonMangoldtMajorant eta k n := by
    unfold gallagherWeight weightedVonMangoldtMajorant
    rw [← hrpow]
    ring
  unfold gallagherBaseCoefficient
  rw [show
    (((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) *
          chi n * Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) *
        (gallagherWeight eta k n : ℂ) =
      (((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ))) *
          gallagherWeight eta k n : ℝ) : ℂ) * chi n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ)) by
      push_cast
      ring]
  rw [hscalar]

/-- The existing variable-band detector is exactly the Abel-weighted sum
of the unweighted partial-sum coefficients. -/
theorem variableBandZeroDetectorPolynomial_eq_gallagherAbelSum
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (E : ℕ) (eta : ℝ) (j N : ℕ) (t : ℝ) :
    variableBandZeroDetectorPolynomial chi E eta j N t =
      ∑ n ∈ Finset.Ioc (variableDetectorLowerCutoff E eta j) N,
        gallagherBaseCoefficient chi t n *
          (gallagherWeight eta (j - 1) n : ℂ) := by
  classical
  unfold variableBandZeroDetectorPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  exact (gallagherBaseCoefficient_mul_weight chi t eta (j - 1)
    (by have := (Finset.mem_Ioc.mp hn).1; omega : 0 < n)).symm

/-- An explicit pointwise majorant for the derivative on `[n,n+1]`. -/
noncomputable def gallagherLogDerivativeMajorant
    (eta : ℝ) (k n : ℕ) : ℝ :=
  (k : ℝ) * Real.log (n + 1) ^ (k - 1) +
    eta * Real.log (n + 1) ^ k

noncomputable def gallagherWeightSlopeMajorant
    (eta : ℝ) (k n : ℕ) : ℝ :=
  gallagherLogDerivativeMajorant eta k n * (n : ℝ) ^ (-eta - 1)

theorem norm_deriv_smoothGallagherWeight_le_slopeMajorant
    {eta : ℝ} (heta : 0 ≤ eta) (k : ℕ) {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : x ∈ Set.Icc (n : ℝ) (n + 1 : ℕ)) :
    ‖deriv (smoothGallagherWeight eta k) x‖ ≤
      gallagherWeightSlopeMajorant eta k n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := hnR.trans_le hx.1
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log x :=
    Real.log_nonneg (hnOne.trans hx.1)
  have hlogn0 : 0 ≤ Real.log (n + 1 : ℕ) :=
    Real.log_natCast_nonneg (n + 1)
  have hlogle : Real.log x ≤ Real.log (n + 1 : ℕ) := by
    apply Real.log_le_log hx0
    exact hx.2
  have hrpow : x ^ (-eta - 1) ≤ (n : ℝ) ^ (-eta - 1) := by
    exact Real.rpow_le_rpow_of_nonpos hnR hx.1 (by linarith)
  have ha0 : 0 ≤ (k : ℝ) * Real.log x ^ (k - 1) := by positivity
  have hb0 : 0 ≤ eta * Real.log x ^ k := by positivity
  have habs :
      |(k : ℝ) * Real.log x ^ (k - 1) - eta * Real.log x ^ k| ≤
        (k : ℝ) * Real.log x ^ (k - 1) + eta * Real.log x ^ k := by
    rw [abs_le]
    constructor <;> linarith
  have hbracket :
      (k : ℝ) * Real.log x ^ (k - 1) + eta * Real.log x ^ k ≤
        (k : ℝ) * Real.log (n + 1 : ℕ) ^ (k - 1) +
          eta * Real.log (n + 1 : ℕ) ^ k := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlog0 hlogle (k - 1)) (by positivity))
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hlog0 hlogle k) heta)
  rw [(hasDerivAt_smoothGallagherWeight eta k hx0).deriv,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  unfold gallagherWeightSlopeMajorant gallagherLogDerivativeMajorant
  simp only [Nat.cast_add, Nat.cast_one] at hbracket ⊢
  calc
    x ^ (-eta - 1) *
        |(k : ℝ) * Real.log x ^ (k - 1) - eta * Real.log x ^ k| ≤
      x ^ (-eta - 1) *
        ((k : ℝ) * Real.log x ^ (k - 1) + eta * Real.log x ^ k) := by
        gcongr
    _ ≤ (n : ℝ) ^ (-eta - 1) *
        ((k : ℝ) * Real.log ((n : ℝ) + 1) ^ (k - 1) +
          eta * Real.log ((n : ℝ) + 1) ^ k) := by
        gcongr
    _ = ((k : ℝ) * Real.log ((n : ℝ) + 1) ^ (k - 1) +
          eta * Real.log ((n : ℝ) + 1) ^ k) *
        (n : ℝ) ^ (-eta - 1) := by ring

/-- One-step variation of the discrete weight, obtained from the mean-value
inequality with the preceding sharp local derivative majorant. -/
theorem abs_gallagherWeight_sub_succ_le
    {eta : ℝ} (heta : 0 ≤ eta) (k : ℕ) {n : ℕ} (hn : 0 < n) :
    |gallagherWeight eta k n - gallagherWeight eta k (n + 1)| ≤
      gallagherWeightSlopeMajorant eta k n := by
  let s : Set ℝ := Set.Icc (n : ℝ) (n + 1 : ℕ)
  have hdiff : ∀ x ∈ s, DifferentiableAt ℝ (smoothGallagherWeight eta k) x := by
    intro x hx
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact (hasDerivAt_smoothGallagherWeight eta k
      (hnR.trans_le hx.1)).differentiableAt
  have hbound : ∀ x ∈ s,
      ‖deriv (smoothGallagherWeight eta k) x‖ ≤
        gallagherWeightSlopeMajorant eta k n := by
    intro x hx
    exact norm_deriv_smoothGallagherWeight_le_slopeMajorant heta k hn hx
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc (n : ℝ) (n + 1 : ℕ))
    (show (n : ℝ) ∈ s by exact Set.left_mem_Icc.2 (by norm_num))
    (show ((n + 1 : ℕ) : ℝ) ∈ s by
      exact Set.right_mem_Icc.2 (by norm_num))
  rw [show ‖((n + 1 : ℕ) : ℝ) - (n : ℝ)‖ = 1 by
    push_cast
    norm_num, mul_one] at hmv
  rw [← norm_sub_rev] at hmv
  simpa only [smoothGallagherWeight, gallagherWeight, Real.norm_eq_abs,
    Nat.cast_add, Nat.cast_one] using hmv

/-- Exact finite variation factor occurring after weighted Cauchy--Schwarz. -/
noncomputable def gallagherWeightVariationFactor
    (eta : ℝ) (k A N : ℕ) : ℝ :=
  (N : ℝ) * |gallagherWeight eta k N| ^ 2 +
    ∑ n ∈ Finset.Ico A N,
      (n : ℝ) *
        |gallagherWeight eta k n - gallagherWeight eta k (n + 1)| ^ 2

/-- Fully explicit finite majorant for the cutoff-weight variation.  No
monotonicity assumption on the weight itself is needed, so it applies on
both sides of the saddle point `log n = k/eta`. -/
theorem gallagherWeightVariationFactor_le_slopeSum
    {eta : ℝ} (heta : 0 ≤ eta) (k : ℕ) {A N : ℕ}
    (hA : 0 < A) (hAN : A ≤ N) :
    gallagherWeightVariationFactor eta k A N ≤
      (N : ℝ) * |gallagherWeight eta k N| ^ 2 +
        ∑ n ∈ Finset.Ico A N,
          (n : ℝ) * gallagherWeightSlopeMajorant eta k n ^ 2 := by
  unfold gallagherWeightVariationFactor
  gcongr with n hn
  have hnpos : 0 < n := by
    have hnA := (Finset.mem_Ico.mp hn).1
    omega
  exact abs_gallagherWeight_sub_succ_le heta k hnpos

/-- Multiplication by the logarithmic cutoff measure `n` turns the square
of the local slope into the exact exponent `-2*eta-1`. -/
theorem natCast_mul_gallagherWeightSlopeMajorant_sq
    (eta : ℝ) (k : ℕ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * gallagherWeightSlopeMajorant eta k n ^ 2 =
      gallagherLogDerivativeMajorant eta k n ^ 2 *
        (n : ℝ) ^ (-2 * eta - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let B : ℝ := gallagherLogDerivativeMajorant eta k n
  have hsquare :
      ((n : ℝ) ^ (-eta - 1)) ^ 2 =
        (n : ℝ) ^ ((-eta - 1) * 2) := by
    calc
      ((n : ℝ) ^ (-eta - 1)) ^ 2 =
          ((n : ℝ) ^ (-eta - 1)) ^ (2 : ℝ) :=
        (Real.rpow_two _).symm
      _ = (n : ℝ) ^ ((-eta - 1) * 2) :=
        (Real.rpow_mul hnR.le (-eta - 1) 2).symm
  have hcombine :
      (n : ℝ) * (n : ℝ) ^ ((-eta - 1) * 2) =
        (n : ℝ) ^ (-2 * eta - 1) := by
    calc
      (n : ℝ) * (n : ℝ) ^ ((-eta - 1) * 2) =
          (n : ℝ) ^ (1 : ℝ) *
            (n : ℝ) ^ ((-eta - 1) * 2) := by
              rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + (-eta - 1) * 2) :=
        (Real.rpow_add hnR 1 ((-eta - 1) * 2)).symm
      _ = (n : ℝ) ^ (-2 * eta - 1) := by congr 1 <;> ring
  change (n : ℝ) *
      (B * (n : ℝ) ^ (-eta - 1)) ^ 2 =
    B ^ 2 * (n : ℝ) ^ (-2 * eta - 1)
  rw [mul_pow, hsquare]
  calc
    (n : ℝ) * (B ^ 2 * (n : ℝ) ^ ((-eta - 1) * 2)) =
        B ^ 2 * ((n : ℝ) * (n : ℝ) ^ ((-eta - 1) * 2)) := by ring
    _ = B ^ 2 * (n : ℝ) ^ (-2 * eta - 1) := by rw [hcombine]

/-- The finite variation factor in its sharpest elementary form: one
explicit endpoint term and one finite logarithmic gamma-type sum. -/
theorem gallagherWeightVariationFactor_le_explicitLogSum
    {eta : ℝ} (heta : 0 ≤ eta) (k : ℕ) {A N : ℕ}
    (hA : 0 < A) (hAN : A ≤ N) :
    gallagherWeightVariationFactor eta k A N ≤
      (N : ℝ) * |gallagherWeight eta k N| ^ 2 +
        ∑ n ∈ Finset.Ico A N,
          gallagherLogDerivativeMajorant eta k n ^ 2 *
            (n : ℝ) ^ (-2 * eta - 1) := by
  refine (gallagherWeightVariationFactor_le_slopeSum
    heta k hA hAN).trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact natCast_mul_gallagherWeightSlopeMajorant_sq eta k
    (by have := (Finset.mem_Ico.mp hn).1; omega)

/-- The endpoint term also has an exact closed form. -/
theorem natCast_mul_abs_gallagherWeight_sq
    (eta : ℝ) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * |gallagherWeight eta k N| ^ 2 =
      Real.log N ^ (2 * k) * (N : ℝ) ^ (1 - 2 * eta) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hweight0 : 0 ≤ gallagherWeight eta k N := by
    unfold gallagherWeight
    positivity
  have hlogpow : (Real.log N ^ k) ^ 2 = Real.log N ^ (2 * k) := by
    rw [← pow_mul]
    congr 1
    omega
  have hrpowsq : ((N : ℝ) ^ (-eta)) ^ 2 = (N : ℝ) ^ (-2 * eta) := by
    calc
      ((N : ℝ) ^ (-eta)) ^ 2 =
          ((N : ℝ) ^ (-eta)) ^ (2 : ℝ) := (Real.rpow_two _).symm
      _ = (N : ℝ) ^ ((-eta) * 2) :=
        (Real.rpow_mul hNR.le (-eta) 2).symm
      _ = (N : ℝ) ^ (-2 * eta) := by congr 1 <;> ring
  have hcombine :
      (N : ℝ) * (N : ℝ) ^ (-2 * eta) =
        (N : ℝ) ^ (1 - 2 * eta) := by
    calc
      (N : ℝ) * (N : ℝ) ^ (-2 * eta) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-2 * eta) := by
            rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + (-2 * eta)) :=
        (Real.rpow_add hNR 1 (-2 * eta)).symm
      _ = (N : ℝ) ^ (1 - 2 * eta) := by congr 1 <;> ring
  rw [abs_of_nonneg hweight0]
  unfold gallagherWeight
  rw [mul_pow, hlogpow, hrpowsq]
  calc
    (N : ℝ) * (Real.log N ^ (2 * k) * (N : ℝ) ^ (-2 * eta)) =
        Real.log N ^ (2 * k) *
          ((N : ℝ) * (N : ℝ) ^ (-2 * eta)) := by ring
    _ = Real.log N ^ (2 * k) * (N : ℝ) ^ (1 - 2 * eta) := by
      rw [hcombine]

/-- Completely expanded finite variation bound, exhibiting the exact
gamma-integral exponents that the subsequent summation estimate must pay. -/
theorem gallagherWeightVariationFactor_le_fullyExplicit
    {eta : ℝ} (heta : 0 ≤ eta) (k : ℕ) {A N : ℕ}
    (hA : 0 < A) (hAN : A ≤ N) :
    gallagherWeightVariationFactor eta k A N ≤
      Real.log N ^ (2 * k) * (N : ℝ) ^ (1 - 2 * eta) +
        ∑ n ∈ Finset.Ico A N,
          gallagherLogDerivativeMajorant eta k n ^ 2 *
            (n : ℝ) ^ (-2 * eta - 1) := by
  have hN : 0 < N := hA.trans_le hAN
  simpa only [natCast_mul_abs_gallagherWeight_sq eta k hN] using
    gallagherWeightVariationFactor_le_explicitLogSum heta k hA hAN

/-- The variable detector with its weight removed satisfies the exact
Gallagher partial-sum-energy bound, with the variation factor already
replaced by the explicit derivative majorant. -/
theorem norm_variableBandZeroDetectorPolynomial_sq_le_gallagherEnergy
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (E : ℕ) {eta : ℝ} (heta : 0 ≤ eta) (j N : ℕ) (t : ℝ)
    (hcut : variableDetectorLowerCutoff E eta j ≤ N) :
    ‖variableBandZeroDetectorPolynomial chi E eta j N t‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc (variableDetectorLowerCutoff E eta j) N,
          ‖∑ n ∈ Finset.Ioc (variableDetectorLowerCutoff E eta j) m,
              gallagherBaseCoefficient chi t n‖ ^ 2 / (m : ℝ)) *
        ((N : ℝ) * |gallagherWeight eta (j - 1) N| ^ 2 +
          ∑ n ∈ Finset.Ico (variableDetectorLowerCutoff E eta j) N,
            (n : ℝ) *
              gallagherWeightSlopeMajorant eta (j - 1) n ^ 2) := by
  let A : ℕ := variableDetectorLowerCutoff E eta j
  have hA : 0 < A := by
    dsimp [A, variableDetectorLowerCutoff]
    positivity
  rw [variableBandZeroDetectorPolynomial_eq_gallagherAbelSum]
  have hab :=
    norm_sum_Ioc_mul_sq_le_partialSumEnergy_mul_weightVariation
      (fun n ↦ gallagherBaseCoefficient chi t n)
      (fun n ↦ (gallagherWeight eta (j - 1) n : ℂ)) hA hcut
  have hvar := gallagherWeightVariationFactor_le_slopeSum
    heta (j - 1) hA hcut
  have henergy0 : 0 ≤
      ∑ m ∈ Finset.Icc A N,
        ‖∑ n ∈ Finset.Ioc A m, gallagherBaseCoefficient chi t n‖ ^ 2 /
          (m : ℝ) := by positivity
  refine hab.trans ?_
  apply mul_le_mul_of_nonneg_left _ henergy0
  have hnorm (a b : ℝ) : ‖(a : ℂ) - (b : ℂ)‖ = |a - b| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hnorm0 (a : ℝ) : ‖(a : ℂ)‖ = |a| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  simpa only [A, hnorm, hnorm0, gallagherWeightVariationFactor] using hvar

/-- The same detector estimate with the variation factor completely
expanded into its endpoint and finite gamma-type sum. -/
theorem norm_variableBandZeroDetectorPolynomial_sq_le_fullyExplicitGallagherEnergy
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (E : ℕ) {eta : ℝ} (heta : 0 ≤ eta) (j N : ℕ) (t : ℝ)
    (hcut : variableDetectorLowerCutoff E eta j ≤ N) :
    ‖variableBandZeroDetectorPolynomial chi E eta j N t‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc (variableDetectorLowerCutoff E eta j) N,
          ‖∑ n ∈ Finset.Ioc (variableDetectorLowerCutoff E eta j) m,
              gallagherBaseCoefficient chi t n‖ ^ 2 / (m : ℝ)) *
        (Real.log N ^ (2 * (j - 1)) * (N : ℝ) ^ (1 - 2 * eta) +
          ∑ n ∈ Finset.Ico (variableDetectorLowerCutoff E eta j) N,
            gallagherLogDerivativeMajorant eta (j - 1) n ^ 2 *
              (n : ℝ) ^ (-2 * eta - 1)) := by
  let A : ℕ := variableDetectorLowerCutoff E eta j
  have hA : 0 < A := by
    dsimp [A, variableDetectorLowerCutoff]
    positivity
  rw [variableBandZeroDetectorPolynomial_eq_gallagherAbelSum]
  have hab :=
    norm_sum_Ioc_mul_sq_le_partialSumEnergy_mul_weightVariation
      (fun n ↦ gallagherBaseCoefficient chi t n)
      (fun n ↦ (gallagherWeight eta (j - 1) n : ℂ)) hA hcut
  have hvar := gallagherWeightVariationFactor_le_fullyExplicit
    heta (j - 1) hA hcut
  have henergy0 : 0 ≤
      ∑ m ∈ Finset.Icc A N,
        ‖∑ n ∈ Finset.Ioc A m, gallagherBaseCoefficient chi t n‖ ^ 2 /
          (m : ℝ) := by positivity
  refine hab.trans ?_
  apply mul_le_mul_of_nonneg_left _ henergy0
  have hnorm (a b : ℝ) : ‖(a : ℂ) - (b : ℂ)‖ = |a - b| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hnorm0 (a : ℝ) : ‖(a : ℂ)‖ = |a| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  simpa only [A, hnorm, hnorm0, gallagherWeightVariationFactor] using hvar

end Erdos48
