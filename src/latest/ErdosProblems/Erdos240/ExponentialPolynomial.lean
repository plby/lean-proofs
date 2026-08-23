/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.ComplexTaylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Finite complex exponential polynomials

This file supplies the analytic-function layer used in the auxiliary-function
argument for Erdős Problem 240.  It records exact formulas for ordinary and
divided iterated derivatives of a finite exponential sum, pointwise norm
bounds, and explicit translated Taylor-remainder estimates.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.ExponentialPolynomial

open Finset

variable {I : Type*}

/-- The finite exponential polynomial with coefficients `c i` and exponents
`lambda i`, supported on `s`. -/
def expPoly (s : Finset I) (c lambda : I → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ s, c i * Complex.exp (lambda i * z)

/-- The `n`-th ordinary complex derivative of a finite exponential
polynomial, written explicitly. -/
def ordinaryDerivative (s : Finset I) (c lambda : I → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ s, c i * lambda i ^ n * Complex.exp (lambda i * z)

/-- The divided derivative `F^(n) / n!`. -/
def dividedDerivative (s : Finset I) (c lambda : I → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ordinaryDerivative s c lambda n z / n.factorial

theorem contDiff_expPoly (s : Finset I) (c lambda : I → ℂ) :
    ContDiff ℂ ⊤ (expPoly s c lambda) := by
  apply ContDiff.sum
  intro i hi
  fun_prop

/-- Exact formula for all iterated complex derivatives. -/
theorem iteratedDeriv_expPoly (s : Finset I) (c lambda : I → ℂ)
    (n : ℕ) (z : ℂ) :
    iteratedDeriv n (expPoly s c lambda) z = ordinaryDerivative s c lambda n z := by
  unfold expPoly
  rw [iteratedDeriv_fun_sum]
  · simp only [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul,
      ordinaryDerivative]
    congr 1
    ext i
    ring
  · intro i hi
    fun_prop

/-- The bundled divided derivative agrees with the iterated derivative divided
by the factorial. -/
theorem dividedDerivative_eq_iteratedDeriv_div (s : Finset I) (c lambda : I → ℂ)
    (n : ℕ) (z : ℂ) :
    dividedDerivative s c lambda n z = iteratedDeriv n (expPoly s c lambda) z / n.factorial := by
  rw [iteratedDeriv_expPoly]
  rfl

/-- A termwise triangle-inequality bound for ordinary derivatives. -/
theorem norm_ordinaryDerivative_le (s : Finset I) (c lambda : I → ℂ)
    (n : ℕ) (z : ℂ) :
    ‖ordinaryDerivative s c lambda n z‖ ≤
      ∑ i ∈ s, ‖c i‖ * ‖lambda i‖ ^ n * Real.exp (‖lambda i‖ * ‖z‖) := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi ↦ ?_)
  rw [norm_mul, norm_mul, norm_pow]
  gcongr
  calc
    ‖Complex.exp (lambda i * z)‖ ≤ Real.exp ‖lambda i * z‖ :=
      Complex.norm_exp_le_exp_norm _
    _ = Real.exp (‖lambda i‖ * ‖z‖) := by rw [norm_mul]

/-- The corresponding bound for divided derivatives. -/
theorem norm_dividedDerivative_le (s : Finset I) (c lambda : I → ℂ)
    (n : ℕ) (z : ℂ) :
    ‖dividedDerivative s c lambda n z‖ ≤
      (∑ i ∈ s, ‖c i‖ * ‖lambda i‖ ^ n * Real.exp (‖lambda i‖ * ‖z‖)) /
        n.factorial := by
  rw [dividedDerivative, norm_div]
  rw [Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_ordinaryDerivative_le s c lambda n z)
    (Nat.cast_nonneg n.factorial)

/-- An explicit shifted-point bound, with the displacement and base point
separated by the triangle inequality. -/
theorem norm_ordinaryDerivative_add_le (s : Finset I) (c lambda : I → ℂ)
    (n : ℕ) (w u : ℂ) :
    ‖ordinaryDerivative s c lambda n (w + u)‖ ≤
      ∑ i ∈ s, ‖c i‖ * ‖lambda i‖ ^ n *
        Real.exp (‖lambda i‖ * (‖w‖ + ‖u‖)) := by
  refine (norm_ordinaryDerivative_le s c lambda n (w + u)).trans ?_
  apply sum_le_sum
  intro i hi
  gcongr
  exact norm_add_le w u

/-- A uniform shifted-point bound when all coefficients and exponents are
bounded by `C` and `L`. -/
theorem norm_ordinaryDerivative_add_le_uniform
    (s : Finset I) (c lambda : I → ℂ) (n : ℕ) (w u : ℂ)
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hc : ∀ i ∈ s, ‖c i‖ ≤ C) (hlambda : ∀ i ∈ s, ‖lambda i‖ ≤ L) :
    ‖ordinaryDerivative s c lambda n (w + u)‖ ≤
      s.card * (C * L ^ n * Real.exp (L * (‖w‖ + ‖u‖))) := by
  refine (norm_ordinaryDerivative_add_le s c lambda n w u).trans ?_
  calc
    (∑ i ∈ s, ‖c i‖ * ‖lambda i‖ ^ n *
        Real.exp (‖lambda i‖ * (‖w‖ + ‖u‖))) ≤
        ∑ _i ∈ s, C * L ^ n * Real.exp (L * (‖w‖ + ‖u‖)) := by
      apply sum_le_sum
      intro i hi
      gcongr
      · exact hc i hi
      · exact hlambda i hi
      · exact hlambda i hi
    _ = s.card * (C * L ^ n * Real.exp (L * (‖w‖ + ‖u‖))) := by
      simp

/-- The termwise Taylor polynomial of the `r`-th derivative at `w`, evaluated
at the displacement `u`. -/
def derivativeTaylorApprox (s : Finset I) (c lambda : I → ℂ)
    (r : ℕ) (w u : ℂ) (N : ℕ) : ℂ :=
  ∑ i ∈ s, (c i * lambda i ^ r) * Complex.exp (lambda i * w) *
    ComplexTaylor.expPartialSum (lambda i * u) N

/-- The termwise Taylor approximation is the usual Taylor polynomial in the
higher ordinary derivatives. -/
theorem derivativeTaylorApprox_eq_sum (s : Finset I) (c lambda : I → ℂ)
    (r : ℕ) (w u : ℂ) (N : ℕ) :
    derivativeTaylorApprox s c lambda r w u N =
      ∑ k ∈ range N, ordinaryDerivative s c lambda (r + k) w * u ^ k / k.factorial := by
  simp only [derivativeTaylorApprox, ComplexTaylor.expPartialSum, ordinaryDerivative]
  simp_rw [Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [pow_add, mul_pow]
  ring

/-- Global translated Taylor-remainder bound for any derivative order. -/
theorem norm_ordinaryDerivative_add_sub_taylor_le
    (s : Finset I) (c lambda : I → ℂ) (r : ℕ) (w u : ℂ) (N : ℕ) :
    ‖ordinaryDerivative s c lambda r (w + u) -
        derivativeTaylorApprox s c lambda r w u N‖ ≤
      ∑ i ∈ s, ‖c i‖ * ‖lambda i‖ ^ r * ‖Complex.exp (lambda i * w)‖ *
        (Real.exp ‖lambda i * u‖ * ‖lambda i * u‖ ^ N) := by
  rw [ordinaryDerivative, derivativeTaylorApprox, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi ↦ ?_)
  have hfactor :
      c i * lambda i ^ r * Complex.exp (lambda i * (w + u)) -
          (c i * lambda i ^ r) * Complex.exp (lambda i * w) *
            ComplexTaylor.expPartialSum (lambda i * u) N =
        (c i * lambda i ^ r) *
          (Complex.exp (lambda i * w + lambda i * u) -
            Complex.exp (lambda i * w) *
              ComplexTaylor.expPartialSum (lambda i * u) N) := by
    rw [mul_add]
    ring
  rw [hfactor, norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ (‖c i‖ * ‖lambda i‖ ^ r) *
        (‖Complex.exp (lambda i * w)‖ *
          (Real.exp ‖lambda i * u‖ * ‖lambda i * u‖ ^ N)) :=
      mul_le_mul_of_nonneg_left
        (ComplexTaylor.norm_exp_add_sub_exp_mul_partialSum_le
          (lambda i * w) (lambda i * u) N)
        (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
    _ = _ := by ring

/-- Factorial-strength translated remainder bound in the geometric-decay
range, uniform over all exponent terms. -/
theorem norm_ordinaryDerivative_add_sub_taylor_le_factorial
    (s : Finset I) (c lambda : I → ℂ) (r : ℕ) (w u : ℂ) {N : ℕ}
    (hsmall : ∀ i ∈ s, ‖lambda i * u‖ / N.succ ≤ 1 / 2) :
    ‖ordinaryDerivative s c lambda r (w + u) -
        derivativeTaylorApprox s c lambda r w u N‖ ≤
      ∑ i ∈ s, ‖c i‖ * ‖lambda i‖ ^ r * ‖Complex.exp (lambda i * w)‖ *
        (2 * (‖lambda i * u‖ ^ N / N.factorial)) := by
  rw [ordinaryDerivative, derivativeTaylorApprox, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi ↦ ?_)
  have hfactor :
      c i * lambda i ^ r * Complex.exp (lambda i * (w + u)) -
          (c i * lambda i ^ r) * Complex.exp (lambda i * w) *
            ComplexTaylor.expPartialSum (lambda i * u) N =
        (c i * lambda i ^ r) *
          (Complex.exp (lambda i * w + lambda i * u) -
            Complex.exp (lambda i * w) *
              ComplexTaylor.expPartialSum (lambda i * u) N) := by
    rw [mul_add]
    ring
  rw [hfactor, norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ (‖c i‖ * ‖lambda i‖ ^ r) *
        (‖Complex.exp (lambda i * w)‖ *
          (2 * (‖lambda i * u‖ ^ N / N.factorial))) :=
      mul_le_mul_of_nonneg_left
        (ComplexTaylor.norm_exp_add_sub_exp_mul_partialSum_le_two_mul_div_factorial
          (lambda i * w) (hsmall i hi))
        (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
    _ = _ := by ring

end Erdos240.ExponentialPolynomial
