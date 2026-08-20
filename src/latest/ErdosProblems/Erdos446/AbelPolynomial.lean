/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperElementaryMass
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Erdős Problem 446: Abel polynomials

Ford's ordered-simplex estimates use Abel's convolution identity.  This file
proves the underlying binomial-type identity for the Abel polynomials

`A₀(X) = 1`, `Aₙ(X) = X * (X + n)^(n-1)`.

The proof is polynomial and avoids any appeal to an external combinatorial
enumeration: the derivative recurrence determines the convolution from its
value at zero.
-/

namespace Erdos446

open Finset Polynomial
open scoped BigOperators Polynomial

noncomputable def abelPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * (X + C (n + 1 : ℝ)) ^ n

@[simp] theorem abelPolynomial_zero : abelPolynomial 0 = 1 := rfl

@[simp] theorem abelPolynomial_succ (n : ℕ) :
    abelPolynomial (n + 1) = X * (X + C (n + 1 : ℝ)) ^ n := rfl

@[simp] theorem eval_abelPolynomial_zero (x : ℝ) :
    (abelPolynomial 0).eval x = 1 := by simp

@[simp] theorem eval_abelPolynomial_succ (n : ℕ) (x : ℝ) :
    (abelPolynomial (n + 1)).eval x = x * (x + (n + 1 : ℝ)) ^ n := by
  simp [abelPolynomial]

@[simp] theorem eval_zero_abelPolynomial (n : ℕ) :
    (abelPolynomial n).eval 0 = if n = 0 then 1 else 0 := by
  cases n <;> simp

theorem derivative_abelPolynomial_succ (n : ℕ) :
    derivative (abelPolynomial (n + 1)) =
      C (n + 1 : ℝ) * (abelPolynomial n).comp (X + C 1) := by
  cases n with
  | zero => simp [abelPolynomial]
  | succ n =>
      simp only [abelPolynomial_succ, derivative_mul, derivative_X,
        one_mul, derivative_X_add_C_pow]
      simp [Polynomial.comp]
      simp only [eval₂_pow, eval₂_add, eval₂_one, eval₂_X, eval₂_natCast]
      rw [pow_succ]
      ring

/-- The binomial convolution of two Abel-polynomial sequences, viewed as a
polynomial in the first argument. -/
noncomputable def abelConvolutionPolynomial (n : ℕ) (y : ℝ) : ℝ[X] :=
  ∑ j ∈ range (n + 1),
    C (n.choose j : ℝ) *
      (abelPolynomial j * C ((abelPolynomial (n - j)).eval y))

@[simp] theorem abelConvolutionPolynomial_zero (y : ℝ) :
    abelConvolutionPolynomial 0 y = 1 := by
  simp [abelConvolutionPolynomial]

private theorem derivative_abelConvolutionPolynomial_succ (n : ℕ) (y : ℝ) :
    derivative (abelConvolutionPolynomial (n + 1) y) =
      C (n + 1 : ℝ) *
        (abelConvolutionPolynomial n y).comp (X + C 1) := by
  classical
  rw [abelConvolutionPolynomial, derivative_sum]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, abelPolynomial_zero,
    derivative_mul, derivative_one, zero_mul, derivative_C, mul_zero,
    add_zero, zero_add, derivative_abelPolynomial_succ]
  rw [abelConvolutionPolynomial]
  simp only [Polynomial.sum_comp, mul_comp, C_comp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hsub : n + 1 - (i + 1) = n - i := by omega
  rw [hsub]
  have hchoose :
      ((n + 1).choose (i + 1) : ℝ) * (i + 1 : ℝ) =
        (n + 1 : ℝ) * (n.choose i : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n i).symm
  calc
    C ((n + 1).choose (i + 1) : ℝ) *
          (C (i + 1 : ℝ) * (abelPolynomial i).comp (X + C 1) *
            C ((abelPolynomial (n - i)).eval y)) =
        C (((n + 1).choose (i + 1) : ℝ) * (i + 1 : ℝ)) *
          ((abelPolynomial i).comp (X + C 1) *
            C ((abelPolynomial (n - i)).eval y)) := by
      rw [C_mul]
      ring
    _ = C ((n + 1 : ℝ) * (n.choose i : ℝ)) *
          ((abelPolynomial i).comp (X + C 1) *
            C ((abelPolynomial (n - i)).eval y)) := by rw [hchoose]
    _ = C (n + 1 : ℝ) *
          (C (n.choose i : ℝ) *
            ((abelPolynomial i).comp (X + C 1) *
              C ((abelPolynomial (n - i)).eval y))) := by
      rw [C_mul]
      ring

private theorem polynomial_eq_of_derivative_eq_of_eval_zero
    {p q : ℝ[X]} (hderiv : derivative p = derivative q)
    (heval : p.eval 0 = q.eval 0) : p = q := by
  have hzero : derivative (p - q) = 0 := by
    rw [derivative_sub, hderiv, sub_self]
  have hconst := eq_C_of_derivative_eq_zero hzero
  have hcoeff : (p - q).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, eval_sub]
    exact sub_eq_zero.mpr heval
  rw [hcoeff, C_0] at hconst
  exact sub_eq_zero.mp hconst

/-- Abel polynomials form a sequence of binomial type. -/
theorem abelConvolutionPolynomial_eq (n : ℕ) (y : ℝ) :
    abelConvolutionPolynomial n y =
      (abelPolynomial n).comp (X + C y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      apply polynomial_eq_of_derivative_eq_of_eval_zero
      · rw [derivative_abelConvolutionPolynomial_succ, ih]
        simp only [derivative_comp, derivative_X_add_C, one_mul,
          derivative_abelPolynomial_succ, mul_comp, C_comp, comp_assoc]
        congr 2
        simp [Polynomial.comp]
        ring
      · rw [abelConvolutionPolynomial, Finset.sum_range_succ']
        simp [eval_finsetSum]

/-- Abel's binomial identity in evaluated form. -/
theorem abelPolynomial_binomial (n : ℕ) (x y : ℝ) :
    (∑ j ∈ range (n + 1),
      (n.choose j : ℝ) *
        (abelPolynomial j).eval x *
        (abelPolynomial (n - j)).eval y) =
      (abelPolynomial n).eval (x + y) := by
  calc
    (∑ j ∈ range (n + 1),
        (n.choose j : ℝ) * (abelPolynomial j).eval x *
          (abelPolynomial (n - j)).eval y) =
        (abelConvolutionPolynomial n y).eval x := by
      rw [abelConvolutionPolynomial, eval_finsetSum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [eval_mul, eval_C]
      ring
    _ = ((abelPolynomial n).comp (X + C y)).eval x := by
      rw [abelConvolutionPolynomial_eq]
    _ = (abelPolynomial n).eval (x + y) := by simp

/-! ## The rational kernel used in Ford's convolution -/

noncomputable def abelKernel (x : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then x⁻¹ else (x + n) ^ (n - 1)

theorem eval_abelPolynomial_eq_mul_abelKernel {x : ℝ} (hx : x ≠ 0)
    (n : ℕ) :
    (abelPolynomial n).eval x = x * abelKernel x n := by
  cases n with
  | zero => simp [abelKernel, hx]
  | succ n => simp [abelKernel]

/-- Abel's exact convolution, including both endpoint terms through the
inverse convention in `abelKernel`. -/
theorem abelKernel_convolution (m : ℕ) {A B : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    (∑ j ∈ range (m + 2),
      ((m + 1).choose j : ℝ) * abelKernel A j *
        abelKernel B (m + 1 - j)) =
      (A⁻¹ + B⁻¹) * (A + B + (m + 1 : ℝ)) ^ m := by
  have hbinomial := abelPolynomial_binomial (m + 1) A B
  rw [eval_abelPolynomial_succ] at hbinomial
  have hscaled :
      A * B *
          (∑ j ∈ range (m + 2),
            ((m + 1).choose j : ℝ) * abelKernel A j *
              abelKernel B (m + 1 - j)) =
        (A + B) * (A + B + (m + 1 : ℝ)) ^ m := by
    calc
      A * B *
          (∑ j ∈ range (m + 2),
            ((m + 1).choose j : ℝ) * abelKernel A j *
              abelKernel B (m + 1 - j)) =
          ∑ j ∈ range (m + 2),
            ((m + 1).choose j : ℝ) *
              (abelPolynomial j).eval A *
              (abelPolynomial (m + 1 - j)).eval B := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [eval_abelPolynomial_eq_mul_abelKernel hA,
          eval_abelPolynomial_eq_mul_abelKernel hB]
        ring
      _ = (A + B) * (A + B + (m + 1 : ℝ)) ^ m := hbinomial
  calc
    (∑ j ∈ range (m + 2),
        ((m + 1).choose j : ℝ) * abelKernel A j *
          abelKernel B (m + 1 - j)) =
        ((A + B) * (A + B + (m + 1 : ℝ)) ^ m) / (A * B) :=
      (eq_div_iff (mul_ne_zero hA hB)).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
    _ = (A⁻¹ + B⁻¹) * (A + B + (m + 1 : ℝ)) ^ m := by
      field_simp [hA, hB]
      ring

end Erdos446
