/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovPyke

/-!
# Erdős Problem 446: the signed Abel tail in Pyke's formula

This file proves the second Abel identity

`sum_i choose n i * A_i(x) * (y-i)^(n-i) = (x+y)^n`

and uses it to rewrite Pyke's positive last-failure formula as a short
signed tail.  The latter has only `u+1` terms when `u+v=k+w`.
-/

namespace Erdos446

open Finset Polynomial
open scoped BigOperators Polynomial

/-- The polynomial occurring on the left side of Abel's second identity. -/
noncomputable def abelSecondPolynomial (n : ℕ) (y : ℝ) : ℝ[X] :=
  ∑ i ∈ range (n + 1),
    C (n.choose i : ℝ) *
      (abelPolynomial i * C ((y - (i : ℝ)) ^ (n - i)))

@[simp] theorem abelSecondPolynomial_zero (y : ℝ) :
    abelSecondPolynomial 0 y = 1 := by
  simp [abelSecondPolynomial]

private theorem derivative_abelSecondPolynomial_succ (n : ℕ) (y : ℝ) :
    derivative (abelSecondPolynomial (n + 1) y) =
      C (n + 1 : ℝ) *
        (abelSecondPolynomial n (y - 1)).comp (X + C 1) := by
  classical
  rw [abelSecondPolynomial, derivative_sum]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, abelPolynomial_zero,
    derivative_mul, derivative_one, zero_mul, derivative_C, mul_zero,
    add_zero, zero_add, derivative_abelPolynomial_succ]
  rw [abelSecondPolynomial]
  simp only [Polynomial.sum_comp, mul_comp, C_comp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hsub : n + 1 - (i + 1) = n - i := by omega
  rw [hsub]
  have hbase : y - (i + 1 : ℕ) = (y - 1) - (i : ℝ) := by
    push_cast
    ring
  rw [hbase]
  have hchoose :
      ((n + 1).choose (i + 1) : ℝ) * (i + 1 : ℝ) =
        (n + 1 : ℝ) * (n.choose i : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n i).symm
  calc
    C ((n + 1).choose (i + 1) : ℝ) *
          (C (i + 1 : ℝ) * (abelPolynomial i).comp (X + C 1) *
            C (((y - 1) - (i : ℝ)) ^ (n - i))) =
        C (((n + 1).choose (i + 1) : ℝ) * (i + 1 : ℝ)) *
          ((abelPolynomial i).comp (X + C 1) *
            C (((y - 1) - (i : ℝ)) ^ (n - i))) := by
      rw [C_mul]
      ring
    _ = C ((n + 1 : ℝ) * (n.choose i : ℝ)) *
          ((abelPolynomial i).comp (X + C 1) *
            C (((y - 1) - (i : ℝ)) ^ (n - i))) := by rw [hchoose]
    _ = C (n + 1 : ℝ) *
          (C (n.choose i : ℝ) *
            ((abelPolynomial i).comp (X + C 1) *
              C (((y - 1) - (i : ℝ)) ^ (n - i)))) := by
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

/-- Abel's second polynomial identity. -/
theorem abelSecondPolynomial_eq (n : ℕ) (y : ℝ) :
    abelSecondPolynomial n y = (X + C y) ^ n := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      apply polynomial_eq_of_derivative_eq_of_eval_zero
      · rw [derivative_abelSecondPolynomial_succ, ih]
        have hcomp :
            ((X + C (y - 1)) ^ n).comp (X + C 1) =
              (X + C y) ^ n := by
          rw [pow_comp]
          congr 1
          simp [Polynomial.comp]
        rw [hcomp]
        simp [derivative_pow]
      · rw [abelSecondPolynomial, Finset.sum_range_succ']
        simp [eval_finsetSum]

/-- Abel's second identity in evaluated form. -/
theorem abelPolynomial_second_identity (n : ℕ) (x y : ℝ) :
    (∑ i ∈ range (n + 1),
      (n.choose i : ℝ) * (abelPolynomial i).eval x *
        (y - (i : ℝ)) ^ (n - i)) =
      (x + y) ^ n := by
  calc
    (∑ i ∈ range (n + 1),
        (n.choose i : ℝ) * (abelPolynomial i).eval x *
          (y - (i : ℝ)) ^ (n - i)) =
        (abelSecondPolynomial n y).eval x := by
      rw [abelSecondPolynomial, eval_finsetSum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [eval_mul, eval_C]
      ring
    _ = ((X + C y) ^ n).eval x := by rw [abelSecondPolynomial_eq]
    _ = (x + y) ^ n := by simp

/-- Abel's second identity written with Ford's rational kernel. -/
theorem abelKernel_second_identity (n : ℕ) {x y : ℝ} (hx : x ≠ 0) :
    (∑ i ∈ range (n + 1),
      (n.choose i : ℝ) * x * abelKernel x i *
        (y - (i : ℝ)) ^ (n - i)) =
      (x + y) ^ n := by
  simpa only [eval_abelPolynomial_eq_mul_abelKernel hx, mul_assoc] using
    abelPolynomial_second_identity n x y

/-! ## The short signed tail -/

/-- A summand in the second Abel identity, in the normalization occurring
in Pyke's formula.  Unlike the last-failure terms, this definition retains
the signed real difference `q-i`. -/
noncomputable def abelPykeSignedTerm (k w q i : ℕ) : ℝ :=
  (k.choose i : ℝ) * (w : ℝ) * abelKernel (w : ℝ) i *
    ((q : ℝ) - (i : ℝ)) ^ (k - i)

theorem sum_abelPykeSignedTerm (k q : ℕ) {w : ℕ} (hw : 0 < w) :
    (∑ i ∈ range (k + 1), abelPykeSignedTerm k w q i) =
      (w + q : ℕ) ^ k := by
  have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  simpa only [abelPykeSignedTerm, Nat.cast_add, Nat.cast_pow] using
    abelKernel_second_identity k (x := (w : ℝ)) (y := (q : ℝ)) hwR

/-- The positive last-failure part of Pyke's formula is precisely the
initial, hence nonnegative, segment of Abel's second identity. -/
theorem pykeFailureSum_eq_abelPrefix
    {k u w : ℕ} (huk : u ≤ k) :
    (∑ h ∈ Finset.Icc 1 (k - u),
        (k.choose (u + h) : ℝ) * (w : ℝ) *
          abelKernel (w : ℝ) (k - (u + h)) *
            (h : ℝ) ^ (u + h)) =
      ∑ i ∈ range (k - u), abelPykeSignedTerm k w (k - u) i := by
  classical
  apply Finset.sum_bij (fun h _ ↦ k - u - h)
  · intro h hh
    rw [Finset.mem_range]
    have hhData := Finset.mem_Icc.mp hh
    omega
  · intro h₁ hh₁ h₂ hh₂ heq
    have hh₁Data := Finset.mem_Icc.mp hh₁
    have hh₂Data := Finset.mem_Icc.mp hh₂
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    refine ⟨k - u - i, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro h hh
    have hhData := Finset.mem_Icc.mp hh
    have huhk : u + h ≤ k := by omega
    have hindex : k - (u + h) = k - u - h := by omega
    have hexponent : k - (k - u - h) = u + h := by omega
    have hbase :
        ((k - u : ℕ) : ℝ) - ((k - u - h : ℕ) : ℝ) = (h : ℝ) := by
      rw [Nat.cast_sub hhData.2]
      ring
    rw [abelPykeSignedTerm, ← Nat.choose_symm huhk, hindex,
      hexponent, hbase]

/-- Pyke's exact formula as a signed Abel tail.  Since the lower endpoint
is `k-u`, the right side contains exactly `u+1` summands. -/
theorem smirnovOccupancyMass_eq_abelTail
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (huk : u ≤ k) :
    (k.factorial : ℝ) * smirnovOccupancyMass k u v =
      ∑ i ∈ Finset.Ico (k - u) (k + 1),
        abelPykeSignedTerm k w (k - u) i := by
  have hpyke := smirnovOccupancyMass_pyke_last_failure hw hrel huk
  rw [pykeFailureSum_eq_abelPrefix huk] at hpyke
  have hfull := sum_abelPykeSignedTerm k (k - u) hw
  have hv : w + (k - u) = v := by omega
  rw [hv] at hfull
  have hsplit := sum_range_add_sum_Ico
    (f := abelPykeSignedTerm k w (k - u))
    (show k - u ≤ k + 1 by omega)
  rw [hfull] at hsplit
  linarith

/-- Reflection about the upper endpoint turns the Abel tail into a sum over
`j=0,…,u`; the sign is carried by `(j-u)^j`. -/
theorem sum_abelPykeSignedTerm_tail_reflect
    {k u w : ℕ} (huk : u ≤ k) :
    (∑ i ∈ Finset.Ico (k - u) (k + 1),
        abelPykeSignedTerm k w (k - u) i) =
      ∑ j ∈ range (u + 1),
        (k.choose j : ℝ) * (w : ℝ) *
          abelKernel (w : ℝ) (k - j) *
            ((j : ℝ) - (u : ℝ)) ^ j := by
  classical
  apply Finset.sum_bij (fun i _ ↦ k - i)
  · intro i hi
    rw [Finset.mem_range]
    have hiData := Finset.mem_Ico.mp hi
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    have hi₁Data := Finset.mem_Ico.mp hi₁
    have hi₂Data := Finset.mem_Ico.mp hi₂
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    refine ⟨k - j, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      omega
    · omega
  · intro i hi
    have hiData := Finset.mem_Ico.mp hi
    have hik : i ≤ k := by omega
    have hki : k - (k - i) = i := by omega
    have hbase :
        ((k - u : ℕ) : ℝ) - (i : ℝ) =
          ((k - i : ℕ) : ℝ) - (u : ℝ) := by
      rw [Nat.cast_sub huk, Nat.cast_sub hik]
      ring
    rw [abelPykeSignedTerm, hki, hbase, Nat.choose_symm hik]

/-- Reflected short-tail form of Pyke's exact formula. -/
theorem smirnovOccupancyMass_eq_reflectedAbelTail
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (huk : u ≤ k) :
    (k.factorial : ℝ) * smirnovOccupancyMass k u v =
      ∑ j ∈ range (u + 1),
        (k.choose j : ℝ) * (w : ℝ) *
          abelKernel (w : ℝ) (k - j) *
            ((j : ℝ) - (u : ℝ)) ^ j := by
  rw [smirnovOccupancyMass_eq_abelTail hw hrel huk,
    sum_abelPykeSignedTerm_tail_reflect huk]

/-- Exact short-tail formula after probability normalization. -/
theorem smirnovProbability_eq_reflectedAbelTail
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (huk : u ≤ k) :
    smirnovProbability k u v =
      (∑ j ∈ range (u + 1),
        (k.choose j : ℝ) * (w : ℝ) *
          abelKernel (w : ℝ) (k - j) *
            ((j : ℝ) - (u : ℝ)) ^ j) /
        (v : ℝ) ^ k := by
  rw [smirnovProbability,
    smirnovOccupancyMass_eq_reflectedAbelTail hw hrel huk]

end Erdos446
