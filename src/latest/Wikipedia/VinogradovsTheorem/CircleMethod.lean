/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# Circle-method identities for Erdős Problem 471

This file contains only exact finite Fourier identities. The analytic major-
and minor-arc estimates are developed separately.
-/

noncomputable section

namespace VinogradovsTheorem.CircleMethod

open Finset MeasureTheory

/-- The additive character `e(αm) = exp(2πi αm)`. -/
def addChar (α : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (α : ℂ))

/-- The logarithmically weighted prime exponential sum. -/
def primeLogExpSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
    (Real.log (p : ℝ) : ℂ) * addChar α p

/-- The exact weighted coefficient selected from primes at most `N`. -/
def rawPrimeTripleLogWeight (N n : ℕ) : ℝ :=
  ∑ t ∈ (((Finset.range (N + 1)).filter Nat.Prime) ×ˢ
      ((Finset.range (N + 1)).filter Nat.Prime)) ×ˢ
        ((Finset.range (N + 1)).filter Nat.Prime),
    if t.1.1 + t.1.2 + t.2 = n then
      Real.log (t.1.1 : ℝ) * Real.log (t.1.2 : ℝ) * Real.log (t.2 : ℝ)
    else 0

/-- The von Mangoldt exponential sum.  Unlike the prime-only sum, this also
counts proper prime powers; those form an elementary lower-order tail. -/
def vonMangoldtExpSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ m ∈ Finset.range (N + 1),
    (ArithmeticFunction.vonMangoldt m : ℂ) * addChar α m

/-- The exact ternary von Mangoldt coefficient selected at frequency `n`. -/
def rawVonMangoldtTripleWeight (N n : ℕ) : ℝ :=
  ∑ t ∈ ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)) ×ˢ
      Finset.range (N + 1)),
    if t.1.1 + t.1.2 + t.2 = n then
      ArithmeticFunction.vonMangoldt t.1.1 *
        ArithmeticFunction.vonMangoldt t.1.2 *
          ArithmeticFunction.vonMangoldt t.2
    else 0

theorem addChar_sum_three (α : ℝ) (a b c : ℕ) :
    addChar α (a + b + c) = addChar α a * addChar α b * addChar α c := by
  unfold addChar
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Orthogonality of integral-frequency characters on `[0,1]`. -/
theorem integral_exp_int_freq (k : ℤ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (α : ℂ)) =
        if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hcoeff_zero :
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun _ : ℝ ↦ (1 : ℂ)) (-k) = 0 := by
      have h := fourierCoeffOn_of_hasDerivAt (hab := zero_lt_one)
        (n := -k) (hn := neg_ne_zero.mpr hk)
        (f := fun _ : ℝ ↦ (1 : ℂ)) (f' := fun _ : ℝ ↦ (0 : ℂ))
        (by
          intro x _hx
          simpa using (hasDerivAt_const (x := x) (c := (1 : ℂ))))
        (by
          simp : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℂ)) volume (0 : ℝ) 1)
      have hz :
          fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
            (fun _ : ℝ ↦ (0 : ℂ)) (-k) = 0 := by
        rw [fourierCoeffOn_eq_integral]
        simp
      rw [hz] at h
      simpa using h
    have hcoeff_int := fourierCoeffOn_eq_integral (a := (0 : ℝ)) (b := 1)
      (f := fun _ : ℝ ↦ (1 : ℂ)) (-k) zero_lt_one
    simp only [sub_zero, one_div, inv_one, one_smul] at hcoeff_int
    rw [intervalIntegral.integral_of_le zero_le_one] at hcoeff_int
    rw [← integral_Icc_eq_integral_Ioc] at hcoeff_int
    have hint_zero : ∫ x in Set.Icc (0 : ℝ) 1,
        fourier k (x : AddCircle (1 : ℝ)) = 0 := by
      simpa [hk] using hcoeff_int.symm.trans hcoeff_zero
    rw [if_neg hk]
    convert hint_zero using 2
    ext x
    rw [fourier_coe_apply]
    push_cast
    ring_nf

theorem integral_addChar_kernel (m n : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
      addChar α m *
        Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
          if m = n then 1 else 0 := by
  have horth := integral_exp_int_freq ((m : ℤ) - (n : ℤ))
  have hif :
      (if ((m : ℤ) - (n : ℤ) : ℤ) = 0 then (1 : ℂ) else 0) =
        if m = n then 1 else 0 := by
    split_ifs with h hmn hmn
    · rfl
    · omega
    · omega
    · rfl
  rw [hif] at horth
  rw [← horth]
  apply integral_congr_ae
  filter_upwards with α
  unfold addChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- Exact Fourier inversion for the logarithmically weighted ternary-prime
count. -/
theorem integral_primeLogExpSum_cube_kernel (N n : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
      (primeLogExpSum α N) ^ 3 *
        Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
          (rawPrimeTripleLogWeight N n : ℂ) := by
  let s := (Finset.range (N + 1)).filter Nat.Prime
  have hpoint : ∀ α : ℝ,
      (primeLogExpSum α N) ^ 3 *
          Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
        ∑ t ∈ (s ×ˢ s) ×ˢ s,
          ((Real.log (t.2 : ℝ) : ℂ) * addChar α t.2) *
            ((Real.log (t.1.2 : ℝ) : ℂ) * addChar α t.1.2) *
            ((Real.log (t.1.1 : ℝ) : ℂ) * addChar α t.1.1) *
              Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) := by
    intro α
    dsimp [s]
    unfold primeLogExpSum
    simp_rw [Finset.sum_product]
    simp [pow_succ, mul_sum, sum_mul, mul_assoc]
  have hraw : (rawPrimeTripleLogWeight N n : ℂ) =
      ∑ t ∈ (s ×ˢ s) ×ˢ s,
        ((if t.1.1 + t.1.2 + t.2 = n then
          Real.log (t.1.1 : ℝ) * Real.log (t.1.2 : ℝ) * Real.log (t.2 : ℝ)
        else 0 : ℝ) : ℂ) := by
    dsimp [s]
    unfold rawPrimeTripleLogWeight
    push_cast
    rfl
  rw [setIntegral_congr_fun measurableSet_Icc (fun α _hα ↦ hpoint α)]
  rw [integral_finsetSum]
  · rw [hraw]
    refine Finset.sum_congr rfl ?_
    intro t _ht
    let C : ℂ :=
      (Real.log (t.1.1 : ℝ) : ℂ) * (Real.log (t.1.2 : ℝ) : ℂ) *
        (Real.log (t.2 : ℝ) : ℂ)
    rw [show (∫ α in Set.Icc (0 : ℝ) 1,
          ((Real.log (t.2 : ℝ) : ℂ) * addChar α t.2) *
            ((Real.log (t.1.2 : ℝ) : ℂ) * addChar α t.1.2) *
            ((Real.log (t.1.1 : ℝ) : ℂ) * addChar α t.1.1) *
              Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
        ∫ α in Set.Icc (0 : ℝ) 1,
          C * (addChar α (t.2 + t.1.2 + t.1.1) *
            Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)))) from by
      apply setIntegral_congr_fun measurableSet_Icc
      intro α _hα
      dsimp [C]
      rw [addChar_sum_three]
      ring]
    rw [show (∫ α in Set.Icc (0 : ℝ) 1,
          C * (addChar α (t.2 + t.1.2 + t.1.1) *
            Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ))) =
        C * ∫ α in Set.Icc (0 : ℝ) 1,
          addChar α (t.2 + t.1.2 + t.1.1) *
            Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ))) from by
      rw [← integral_indicator measurableSet_Icc,
        ← integral_indicator measurableSet_Icc]
      simp_rw [Set.indicator_const_mul]
      exact MeasureTheory.integral_const_mul C
        ((Set.Icc (0 : ℝ) 1).indicator fun α ↦
          addChar α (t.2 + t.1.2 + t.1.1) *
            Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)))]
    rw [integral_addChar_kernel]
    have hsum : t.2 + t.1.2 + t.1.1 = t.1.1 + t.1.2 + t.2 := by omega
    rw [hsum]
    dsimp [C]
    split_ifs <;> push_cast <;> ring
  · intro t _ht
    apply Continuous.integrableOn_Icc
    unfold addChar
    fun_prop

/-- Exact Fourier inversion for the ternary von Mangoldt coefficient. -/
theorem integral_vonMangoldtExpSum_cube_kernel (N n : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
      (vonMangoldtExpSum α N) ^ 3 *
        Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
          (rawVonMangoldtTripleWeight N n : ℂ) := by
  let s := Finset.range (N + 1)
  have hpoint : ∀ α : ℝ,
      (vonMangoldtExpSum α N) ^ 3 *
          Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
        ∑ t ∈ (s ×ˢ s) ×ˢ s,
          ((ArithmeticFunction.vonMangoldt t.2 : ℂ) * addChar α t.2) *
            ((ArithmeticFunction.vonMangoldt t.1.2 : ℂ) * addChar α t.1.2) *
            ((ArithmeticFunction.vonMangoldt t.1.1 : ℂ) * addChar α t.1.1) *
              Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) := by
    intro α
    dsimp [s]
    unfold vonMangoldtExpSum
    simp_rw [Finset.sum_product]
    simp [pow_succ, mul_sum, sum_mul, mul_assoc]
  have hraw : (rawVonMangoldtTripleWeight N n : ℂ) =
      ∑ t ∈ (s ×ˢ s) ×ˢ s,
        ((if t.1.1 + t.1.2 + t.2 = n then
          ArithmeticFunction.vonMangoldt t.1.1 *
            ArithmeticFunction.vonMangoldt t.1.2 *
              ArithmeticFunction.vonMangoldt t.2
        else 0 : ℝ) : ℂ) := by
    dsimp [s]
    unfold rawVonMangoldtTripleWeight
    push_cast
    rfl
  rw [setIntegral_congr_fun measurableSet_Icc (fun α _hα ↦ hpoint α)]
  rw [integral_finsetSum]
  · rw [hraw]
    refine Finset.sum_congr rfl ?_
    intro t _ht
    let C : ℂ :=
      (ArithmeticFunction.vonMangoldt t.1.1 : ℂ) *
        (ArithmeticFunction.vonMangoldt t.1.2 : ℂ) *
          (ArithmeticFunction.vonMangoldt t.2 : ℂ)
    rw [show (∫ α in Set.Icc (0 : ℝ) 1,
          ((ArithmeticFunction.vonMangoldt t.2 : ℂ) * addChar α t.2) *
            ((ArithmeticFunction.vonMangoldt t.1.2 : ℂ) * addChar α t.1.2) *
            ((ArithmeticFunction.vonMangoldt t.1.1 : ℂ) * addChar α t.1.1) *
              Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
        ∫ α in Set.Icc (0 : ℝ) 1,
          C * (addChar α (t.2 + t.1.2 + t.1.1) *
            Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)))) from by
      apply setIntegral_congr_fun measurableSet_Icc
      intro α _hα
      dsimp [C]
      rw [addChar_sum_three]
      ring]
    rw [show (∫ α in Set.Icc (0 : ℝ) 1,
          C * (addChar α (t.2 + t.1.2 + t.1.1) *
            Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ))) =
        C * ∫ α in Set.Icc (0 : ℝ) 1,
          addChar α (t.2 + t.1.2 + t.1.1) *
            Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ))) from by
      rw [← integral_indicator measurableSet_Icc,
        ← integral_indicator measurableSet_Icc]
      simp_rw [Set.indicator_const_mul]
      exact MeasureTheory.integral_const_mul C
        ((Set.Icc (0 : ℝ) 1).indicator fun α ↦
          addChar α (t.2 + t.1.2 + t.1.1) *
            Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)))]
    rw [integral_addChar_kernel]
    have hsum : t.2 + t.1.2 + t.1.1 = t.1.1 + t.1.2 + t.2 := by omega
    rw [hsum]
    dsimp [C]
    split_ifs <;> push_cast <;> ring
  · intro t _ht
    apply Continuous.integrableOn_Icc
    unfold addChar
    fun_prop

#print axioms integral_primeLogExpSum_cube_kernel
#print axioms integral_vonMangoldtExpSum_cube_kernel

end VinogradovsTheorem.CircleMethod
