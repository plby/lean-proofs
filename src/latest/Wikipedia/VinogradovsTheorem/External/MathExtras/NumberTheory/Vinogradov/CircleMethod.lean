/-
This file is derived from Gershon Bialer's ternary-Goldbach development.

The reused upstream material was released under the Apache License,
Version 2.0, as described in the file LICENSE. This file has been modified.
The upstream copyright and author notices are retained below.

Copyright (c) 2026 Gershon Bialer. All rights reserved.
-/
import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Wikipedia.VinogradovsTheorem.External.MathExtras.NumberTheory.Vinogradov.Bilinear

/-!
# Circle-Method Infrastructure for Vinogradov-Style Arguments

This file collects reusable definitions and elementary lemmas for finite
Fourier sums used in the ternary Goldbach formalization. The hard analytic
estimates remain in `Bilinear.lean` and `MajorArc.lean`; this module supplies
the common language they should use.

The key convention is

`addChar α n = exp(2π i n α)`.

## Main definitions

* `addChar` — additive character on `ℝ / ℤ`, evaluated at a natural frequency.
* `primeExpSum` — unweighted prime exponential sum.
* `vonMangoldtExpSum` — von-Mangoldt weighted exponential sum.
* `majorArcCenters`, `majorArcs`, `minorArcs` — basic arc decomposition.

## Status

L2-style elementary infrastructure: no own proof holes.
-/

namespace Vinogradov

open Finset
open MeasureTheory

/-- Additive character `e(nα) = exp(2π i n α)`. -/
noncomputable def addChar (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (α : ℂ))

/-- The conjugate-frequency character `e(-nα)`, written explicitly to avoid
choosing a quotient-circle convention in later `L²` kernels. -/
noncomputable def negAddChar (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ))

/-- The unweighted prime exponential sum `∑_{p ≤ N, p prime} e(pα)`. -/
noncomputable def primeExpSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, addChar α p

/-- The von-Mangoldt weighted exponential sum `∑_{n ≤ N} Λ(n)e(nα)`. -/
noncomputable def vonMangoldtExpSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    (ArithmeticFunction.vonMangoldt n : ℂ) * addChar α n

/-- Major-arc centers `a/q` with `q ≤ Q`, `q ≠ 0`, `0 ≤ a < q`, `(a,q)=1`. -/
def majorArcCenters (Q : ℕ) : Set (ℕ × ℕ) :=
  { aq | aq.2 ≤ Q ∧ aq.2 ≠ 0 ∧ aq.1 < aq.2 ∧ Nat.Coprime aq.1 aq.2 }

/-- Major arcs inside `[0,1]`: points close to some reduced rational `a/q`. -/
noncomputable def majorArcs (N Q : ℕ) : Set ℝ :=
  { α | α ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ a q : ℕ, (a, q) ∈ majorArcCenters Q ∧
        |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * N) }

/-- Minor arcs are the complement of the major arcs inside `[0,1]`. -/
noncomputable def minorArcs (N Q : ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 \ majorArcs N Q

/-! ## Additive-character identities -/

@[simp] theorem addChar_zero_left (n : ℕ) : addChar 0 n = 1 := by
  unfold addChar
  simp [Complex.exp_zero]

@[simp] theorem addChar_zero_right (α : ℝ) : addChar α 0 = 1 := by
  unfold addChar
  simp [Complex.exp_zero]

theorem addChar_periodic (α : ℝ) (n : ℕ) : addChar (α + 1) n = addChar α n := by
  unfold addChar
  have h : (2 * Real.pi * Complex.I * (n : ℂ) * ((α + 1 : ℝ) : ℂ))
        = 2 * Real.pi * Complex.I * (n : ℂ) * (α : ℂ)
          + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem addChar_sub_one (α : ℝ) (n : ℕ) : addChar (α - 1) n = addChar α n := by
  have h := addChar_periodic (α - 1) n
  rw [sub_add_cancel] at h
  exact h.symm

theorem addChar_add_nat (α : ℝ) (m n : ℕ) :
    addChar (α + m) n = addChar α n := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hα : α + ((m + 1 : ℕ) : ℝ) = (α + (m : ℝ)) + 1 := by
        push_cast
        ring
      rw [hα, addChar_periodic, ih]

theorem addChar_sub_nat (α : ℝ) (m n : ℕ) :
    addChar (α - m) n = addChar α n := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hα : α - ((m + 1 : ℕ) : ℝ) = (α - (m : ℝ)) - 1 := by
        push_cast
        ring
      rw [hα, addChar_sub_one, ih]

theorem addChar_add_int (α : ℝ) (k : ℤ) (n : ℕ) :
    addChar (α + k) n = addChar α n := by
  rcases Int.lt_or_le 0 k with hk | hk
  · have hcast : ((k : ℝ)) = (k.toNat : ℝ) := by
      rw [show (k : ℝ) = ((k.toNat : ℤ) : ℝ) from by
        rw [Int.toNat_of_nonneg (le_of_lt hk)]]
      push_cast
      rfl
    rw [hcast]
    exact addChar_add_nat α k.toNat n
  · have hcast : ((k : ℝ)) = -((-k).toNat : ℝ) := by
      rw [show (k : ℝ) = -(((-k).toNat : ℤ) : ℝ) from by
        rw [Int.toNat_of_nonneg (Int.neg_nonneg.mpr hk)]
        push_cast
        ring]
      push_cast
      rfl
    rw [hcast]
    have hα : α + -((-k).toNat : ℝ) = α - ((-k).toNat : ℝ) := by ring
    rw [hα]
    exact addChar_sub_nat α (-k).toNat n

@[simp] theorem norm_addChar (α : ℝ) (n : ℕ) : ‖addChar α n‖ = 1 := by
  unfold addChar
  have h :
      2 * Real.pi * Complex.I * (n : ℂ) * (α : ℂ)
        = ((2 * Real.pi * n * α : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem addChar_ne_zero (α : ℝ) (n : ℕ) : addChar α n ≠ 0 := by
  unfold addChar
  exact Complex.exp_ne_zero _

@[simp] theorem negAddChar_zero_left (n : ℕ) : negAddChar 0 n = 1 := by
  unfold negAddChar
  simp [Complex.exp_zero]

@[simp] theorem negAddChar_zero_right (α : ℝ) : negAddChar α 0 = 1 := by
  unfold negAddChar
  simp [Complex.exp_zero]

theorem negAddChar_periodic (α : ℝ) (n : ℕ) :
    negAddChar (α + 1) n = negAddChar α n := by
  unfold negAddChar
  have h : -2 * Real.pi * Complex.I * (((α + 1 : ℝ) : ℂ)) * (n : ℂ)
        = -2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)
          - (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_sub, Complex.exp_nat_mul_two_pi_mul_I]
  simp

@[simp] theorem norm_negAddChar (α : ℝ) (n : ℕ) : ‖negAddChar α n‖ = 1 := by
  unfold negAddChar
  have h :
      -2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)
        = ((-2 * Real.pi * α * n : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- Conjugation: `conj (addChar α n) = negAddChar α n`. -/
theorem conj_addChar_eq_negAddChar (α : ℝ) (n : ℕ) :
    starRingEnd ℂ (addChar α n) = negAddChar α n := by
  unfold addChar negAddChar
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul, map_mul]
  rw [Complex.conj_I]
  rw [show starRingEnd ℂ (2 : ℂ) = (2 : ℂ) from by
        rw [show ((2 : ℂ) : ℂ) = ((2 : ℝ) : ℂ) from by norm_num]
        exact Complex.conj_ofReal _]
  rw [show starRingEnd ℂ ((Real.pi : ℂ)) = (Real.pi : ℂ) from
        Complex.conj_ofReal _]
  rw [show starRingEnd ℂ ((n : ℂ)) = (n : ℂ) from by simp]
  rw [show starRingEnd ℂ ((α : ℂ)) = (α : ℂ) from
        Complex.conj_ofReal _]
  ring

theorem addChar_add_right (α : ℝ) (m n : ℕ) :
    addChar α (m + n) = addChar α m * addChar α n := by
  unfold addChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem addChar_sum_three (α : ℝ) (a b c : ℕ) :
    addChar α (a + b + c) = addChar α a * addChar α b * addChar α c := by
  rw [addChar_add_right, addChar_add_right]

theorem integral_exp_int_freq (k : ℤ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (α : ℂ)) =
        if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hcoeff_zero :
        fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
          (fun _ : ℝ => (1 : ℂ)) (-k) = 0 := by
      have h := fourierCoeffOn_of_hasDerivAt (hab := zero_lt_one)
        (n := -k) (hn := neg_ne_zero.mpr hk)
        (f := fun _ : ℝ => (1 : ℂ)) (f' := fun _ : ℝ => (0 : ℂ))
        (by
          intro x _hx
          simpa using (hasDerivAt_const (x := x) (c := (1 : ℂ))))
        (by
          simp : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume (0 : ℝ) 1)
      have hz :
          fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
            (fun _ : ℝ => (0 : ℂ)) (-k) = 0 := by
        rw [fourierCoeffOn_eq_integral]
        simp
      rw [hz] at h
      simpa using h
    have hcoeff_int := fourierCoeffOn_eq_integral (a := (0 : ℝ)) (b := 1)
      (f := fun _ : ℝ => (1 : ℂ)) (-k) zero_lt_one
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
      addChar α m * Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
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

theorem integral_addChar_negAddChar_kernel (m n : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1, addChar α m * negAddChar α n =
      if m = n then 1 else 0 := by
  simpa [negAddChar] using integral_addChar_kernel m n

/-- Exact `L²` orthogonality for the unweighted prime exponential sum, stated
with the negative-frequency sum explicitly. This is the finite identity behind
the standard `∫ |S(α)|² = π(N)` estimate. -/
theorem integral_primeExpSum_mul_neg_kernel (N : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
      primeExpSum α N *
        (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, negAddChar α p) =
      (((Finset.range (N + 1)).filter Nat.Prime).card : ℂ) := by
  let s := (Finset.range (N + 1)).filter Nat.Prime
  have hpoint : ∀ α : ℝ,
      primeExpSum α N * (∑ p ∈ s, negAddChar α p) =
        ∑ x ∈ s ×ˢ s, addChar α x.2 * negAddChar α x.1 := by
    intro α
    dsimp [s]
    unfold primeExpSum
    simp_rw [Finset.sum_product]
    simp [Finset.mul_sum, Finset.sum_mul]
  rw [setIntegral_congr_fun measurableSet_Icc (fun α _hα => hpoint α)]
  rw [integral_finsetSum]
  · rw [show (∑ x ∈ s ×ˢ s,
          ∫ α in Set.Icc (0 : ℝ) 1, addChar α x.2 * negAddChar α x.1) =
        ∑ x ∈ s ×ˢ s, (if x.2 = x.1 then (1 : ℂ) else 0) from by
      refine Finset.sum_congr rfl ?_
      intro x _hx
      rw [integral_addChar_negAddChar_kernel]]
    have hdiag :
        (s ×ˢ s).filter (fun x : ℕ × ℕ => x.2 = x.1) =
          s.map ⟨fun p => (p, p), by
            intro p q hpq
            exact Prod.ext_iff.mp hpq |>.1⟩ := by
      ext x
      constructor
      · intro hx
        have hxprod : x ∈ s ×ˢ s := (Finset.mem_filter.mp hx).1
        have hxeq : x.2 = x.1 := (Finset.mem_filter.mp hx).2
        have hxprod' : x.1 ∈ s ∧ x.2 ∈ s := by
          simpa using hxprod
        refine Finset.mem_map.mpr ⟨x.1, hxprod'.1, ?_⟩
        apply Prod.ext
        · rfl
        · exact hxeq.symm
      · intro hx
        rcases Finset.mem_map.mp hx with ⟨p, hp, hpx⟩
        rw [← hpx, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hp, hp⟩, rfl⟩
    rw [← Finset.sum_filter, hdiag]
    simp [s]
  · intro x _hx
    apply Continuous.integrableOn_Icc
    unfold addChar negAddChar
    fun_prop

/-- Exact `L²` orthogonality for von-Mangoldt sums. The right side is the
finite second moment of the von-Mangoldt weights. -/
theorem integral_vonMangoldtExpSum_mul_neg_kernel (N : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
      vonMangoldtExpSum α N *
        (∑ n ∈ Finset.range (N + 1),
          (ArithmeticFunction.vonMangoldt n : ℂ) * negAddChar α n) =
      ∑ n ∈ Finset.range (N + 1),
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          (ArithmeticFunction.vonMangoldt n : ℂ)) := by
  let s := Finset.range (N + 1)
  have hpoint : ∀ α : ℝ,
      vonMangoldtExpSum α N *
        (∑ n ∈ s, (ArithmeticFunction.vonMangoldt n : ℂ) * negAddChar α n) =
        ∑ x ∈ s ×ˢ s,
          ((ArithmeticFunction.vonMangoldt x.1 : ℂ) *
            (ArithmeticFunction.vonMangoldt x.2 : ℂ)) *
              (addChar α x.2 * negAddChar α x.1) := by
    intro α
    dsimp [s]
    unfold vonMangoldtExpSum
    simp_rw [Finset.sum_product]
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [setIntegral_congr_fun measurableSet_Icc (fun α _hα => hpoint α)]
  rw [integral_finsetSum]
  · rw [show (∑ x ∈ s ×ˢ s,
          ∫ α in Set.Icc (0 : ℝ) 1,
            ((ArithmeticFunction.vonMangoldt x.1 : ℂ) *
              (ArithmeticFunction.vonMangoldt x.2 : ℂ)) *
                (addChar α x.2 * negAddChar α x.1)) =
        ∑ x ∈ s ×ˢ s,
          ((ArithmeticFunction.vonMangoldt x.1 : ℂ) *
            (ArithmeticFunction.vonMangoldt x.2 : ℂ)) *
              (if x.2 = x.1 then (1 : ℂ) else 0) from by
      refine Finset.sum_congr rfl ?_
      intro x _hx
      let C : ℂ :=
        (ArithmeticFunction.vonMangoldt x.1 : ℂ) *
          (ArithmeticFunction.vonMangoldt x.2 : ℂ)
      rw [show (∫ α in Set.Icc (0 : ℝ) 1,
            ((ArithmeticFunction.vonMangoldt x.1 : ℂ) *
              (ArithmeticFunction.vonMangoldt x.2 : ℂ)) *
                (addChar α x.2 * negAddChar α x.1)) =
          C * ∫ α in Set.Icc (0 : ℝ) 1,
            addChar α x.2 * negAddChar α x.1 from by
        dsimp [C]
        rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
        simp_rw [Set.indicator_const_mul]
        exact MeasureTheory.integral_const_mul
          ((ArithmeticFunction.vonMangoldt x.1 : ℂ) *
            (ArithmeticFunction.vonMangoldt x.2 : ℂ))
          ((Set.Icc (0 : ℝ) 1).indicator
            (fun α => addChar α x.2 * negAddChar α x.1))]
      rw [integral_addChar_negAddChar_kernel]]
    dsimp [s]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp [hx]
  · intro x _hx
    apply Continuous.integrableOn_Icc
    unfold addChar negAddChar
    fun_prop

theorem integral_primeExpSum_cube_kernel (N n : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
      (primeExpSum α N)^3 *
        Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
        ∑ x ∈ ((Finset.range (N + 1)).filter Nat.Prime) ×ˢ
            (((Finset.range (N + 1)).filter Nat.Prime) ×ˢ
              ((Finset.range (N + 1)).filter Nat.Prime)),
          (if x.1 + x.2.1 + x.2.2 = n then (1 : ℂ) else 0) := by
  let s := (Finset.range (N + 1)).filter Nat.Prime
  have hpoint : ∀ α : ℝ,
      (primeExpSum α N)^3 *
          Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
        ∑ x ∈ s ×ˢ (s ×ˢ s),
          addChar α (x.2.2 + x.2.1 + x.1) *
            Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) := by
    intro α
    dsimp [s]
    unfold primeExpSum
    rw [pow_three]
    simp_rw [Finset.sum_product]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _hp
    refine Finset.sum_congr rfl ?_
    intro q _hq
    refine Finset.sum_congr rfl ?_
    intro r _hr
    rw [addChar_sum_three]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc (fun α _hα => hpoint α)]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro x _hx
    rw [integral_addChar_kernel]
    have hsum : x.2.2 + x.2.1 + x.1 = x.1 + x.2.1 + x.2.2 := by omega
    rw [hsum]
  · intro x _hx
    apply Continuous.integrableOn_Icc
    unfold addChar
    fun_prop

theorem integral_vonMangoldtExpSum_cube_kernel (N n : ℕ) :
    ∫ α in Set.Icc (0 : ℝ) 1,
      (vonMangoldtExpSum α N)^3 *
        Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
        ∑ x ∈ (Finset.range (N + 1)) ×ˢ
            ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))),
          ((ArithmeticFunction.vonMangoldt x.1 : ℂ) *
            (ArithmeticFunction.vonMangoldt x.2.1 : ℂ) *
            (ArithmeticFunction.vonMangoldt x.2.2 : ℂ) *
              (if x.1 + x.2.1 + x.2.2 = n then (1 : ℂ) else 0)) := by
  let s := Finset.range (N + 1)
  have hpoint : ∀ α : ℝ,
      (vonMangoldtExpSum α N)^3 *
          Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) =
        ∑ x ∈ s ×ˢ (s ×ˢ s),
          ((ArithmeticFunction.vonMangoldt x.2.2 : ℂ) * addChar α x.2.2) *
            ((ArithmeticFunction.vonMangoldt x.2.1 : ℂ) * addChar α x.2.1) *
            ((ArithmeticFunction.vonMangoldt x.1 : ℂ) * addChar α x.1) *
              Complex.exp (-2 * Real.pi * Complex.I * (α : ℂ) * (n : ℂ)) := by
    intro α
    dsimp [s]
    unfold vonMangoldtExpSum
    simp_rw [Finset.sum_product]
    simp [pow_succ, mul_sum, sum_mul, mul_assoc]
  rw [setIntegral_congr_fun measurableSet_Icc (fun α _hα => hpoint α)]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro x _hx
    let C : ℂ := (ArithmeticFunction.vonMangoldt x.1 : ℂ) *
      (ArithmeticFunction.vonMangoldt x.2.1 : ℂ) *
      (ArithmeticFunction.vonMangoldt x.2.2 : ℂ)
    rw [show (∫ a in Set.Icc (0 : ℝ) 1,
        ((ArithmeticFunction.vonMangoldt x.2.2 : ℂ) * addChar a x.2.2) *
            ((ArithmeticFunction.vonMangoldt x.2.1 : ℂ) * addChar a x.2.1) *
            ((ArithmeticFunction.vonMangoldt x.1 : ℂ) * addChar a x.1) *
              Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ))) =
        ∫ a in Set.Icc (0 : ℝ) 1,
          C * (addChar a (x.2.2 + x.2.1 + x.1) *
              Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ))) from by
      apply setIntegral_congr_fun measurableSet_Icc
      intro a _ha
      dsimp [C]
      rw [addChar_sum_three]
      ring]
    rw [show (∫ a in Set.Icc (0 : ℝ) 1,
          C * (addChar a (x.2.2 + x.2.1 + x.1) *
              Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ)))) =
        C * ∫ a in Set.Icc (0 : ℝ) 1,
          addChar a (x.2.2 + x.2.1 + x.1) *
              Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ)) from by
      rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
      simp_rw [Set.indicator_const_mul]
      exact MeasureTheory.integral_const_mul C ((Set.Icc (0 : ℝ) 1).indicator
        (fun a => addChar a (x.2.2 + x.2.1 + x.1) *
          Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (n : ℂ))))]
    rw [integral_addChar_kernel]
    have hsum : x.2.2 + x.2.1 + x.1 = x.1 + x.2.1 + x.2.2 := by omega
    rw [hsum]
  · intro x _hx
    apply Continuous.integrableOn_Icc
    unfold addChar
    fun_prop

/-! ## Finite exponential-sum identities and bounds -/

@[simp] theorem primeExpSum_zero (N : ℕ) :
    primeExpSum 0 N = (((Finset.range (N + 1)).filter Nat.Prime).card : ℂ) := by
  unfold primeExpSum
  simp

theorem primeExpSum_periodic (α : ℝ) (N : ℕ) :
    primeExpSum (α + 1) N = primeExpSum α N := by
  unfold primeExpSum
  refine Finset.sum_congr rfl ?_
  intro p _
  exact addChar_periodic α p

theorem primeExpSum_add_int (α : ℝ) (N : ℕ) (k : ℤ) :
    primeExpSum (α + k) N = primeExpSum α N := by
  unfold primeExpSum
  refine Finset.sum_congr rfl ?_
  intro p _
  exact addChar_add_int α k p

theorem norm_primeExpSum_le_card (α : ℝ) (N : ℕ) :
    ‖primeExpSum α N‖ ≤ (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) := by
  unfold primeExpSum
  refine (norm_sum_le _ _).trans ?_
  simp

theorem norm_primeExpSum_le_succ (α : ℝ) (N : ℕ) :
    ‖primeExpSum α N‖ ≤ (N + 1 : ℝ) := by
  refine (norm_primeExpSum_le_card α N).trans ?_
  have hcard : ((Finset.range (N + 1)).filter Nat.Prime).card ≤ (Finset.range (N + 1)).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_range] at hcard
  exact_mod_cast hcard

@[simp] theorem vonMangoldtExpSum_zero (N : ℕ) :
    vonMangoldtExpSum 0 N =
      ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℂ) := by
  unfold vonMangoldtExpSum
  simp

theorem vonMangoldtExpSum_periodic (α : ℝ) (N : ℕ) :
    vonMangoldtExpSum (α + 1) N = vonMangoldtExpSum α N := by
  unfold vonMangoldtExpSum
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [addChar_periodic]

theorem vonMangoldtExpSum_add_int (α : ℝ) (N : ℕ) (k : ℤ) :
    vonMangoldtExpSum (α + k) N = vonMangoldtExpSum α N := by
  unfold vonMangoldtExpSum
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [addChar_add_int]

theorem norm_vonMangoldtExpSum_le_sum (α : ℝ) (N : ℕ) :
    ‖vonMangoldtExpSum α N‖ ≤
      ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n := by
  unfold vonMangoldtExpSum
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul, norm_addChar]
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hnorm :
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ =
        ArithmeticFunction.vonMangoldt n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
  rw [hnorm, mul_one]

theorem norm_vonMangoldtExpSum_le_psi (α : ℝ) (N : ℕ) :
    ‖vonMangoldtExpSum α N‖ ≤ Chebyshev.psi N := by
  refine (norm_vonMangoldtExpSum_le_sum α N).trans ?_
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hsum :
      ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n =
        ∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext n
    simp [Finset.mem_range, Finset.mem_Icc]
  rw [hsum]

/-- Compatibility with the older `Vinogradov.expSum` from `Bilinear.lean`. -/
theorem expSum_eq_vonMangoldtExpSum (α : ℝ) (N : ℕ) :
    expSum α N = vonMangoldtExpSum α N := by
  unfold expSum vonMangoldtExpSum addChar
  rfl

/-! ## Arc decomposition lemmas -/

theorem mem_majorArcCenters_iff {Q : ℕ} {a q : ℕ} :
    (a, q) ∈ majorArcCenters Q ↔
      q ≤ Q ∧ q ≠ 0 ∧ a < q ∧ Nat.Coprime a q := Iff.rfl

theorem mem_majorArcs_iff {N Q : ℕ} {α : ℝ} :
    α ∈ majorArcs N Q ↔
      α ∈ Set.Icc (0 : ℝ) 1 ∧
        ∃ a q : ℕ, (a, q) ∈ majorArcCenters Q ∧
          |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * N) := Iff.rfl

theorem mem_minorArcs_iff {N Q : ℕ} {α : ℝ} :
    α ∈ minorArcs N Q ↔ α ∈ Set.Icc (0 : ℝ) 1 ∧ α ∉ majorArcs N Q := by
  unfold minorArcs
  rfl

theorem majorArcs_subset_Icc (N Q : ℕ) :
    majorArcs N Q ⊆ Set.Icc (0 : ℝ) 1 := by
  intro α hα
  exact hα.1

theorem minorArcs_subset_Icc (N Q : ℕ) :
    minorArcs N Q ⊆ Set.Icc (0 : ℝ) 1 := by
  intro α hα
  exact (mem_minorArcs_iff.mp hα).1

theorem majorArcs_disjoint_minorArcs (N Q : ℕ) :
    Disjoint (majorArcs N Q) (minorArcs N Q) := by
  unfold minorArcs
  rw [Set.disjoint_left]
  intro α hmaj hmin
  exact hmin.2 hmaj

theorem Icc_subset_major_union_minor (N Q : ℕ) :
    Set.Icc (0 : ℝ) 1 ⊆ majorArcs N Q ∪ minorArcs N Q := by
  intro α hα
  by_cases hmaj : α ∈ majorArcs N Q
  · exact Or.inl hmaj
  · exact Or.inr ⟨hα, hmaj⟩

theorem major_union_minor_eq_Icc (N Q : ℕ) :
    majorArcs N Q ∪ minorArcs N Q = Set.Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · intro α hα
    rcases hα with hmaj | hmin
    · exact majorArcs_subset_Icc N Q hmaj
    · exact minorArcs_subset_Icc N Q hmin
  · exact Icc_subset_major_union_minor N Q

end Vinogradov
