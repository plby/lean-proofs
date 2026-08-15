/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.RingTheory.PowerSeries.Derivative

/-! # Division-free power-series logarithmic-derivative recurrences -/

namespace Erdos387

open PowerSeries
open scoped PowerSeries

namespace RationalWeil

variable {R : Type*} [CommSemiring R]

theorem coeff_mul_nat_eq_sum_antidiagonal_of_X_mul_derivativeFun_eq_mul
    {L B : R⟦X⟧} (h : X * PowerSeries.derivative R L = L * B) (n : Nat) :
    coeff n L * (n : R) =
      ∑ p ∈ Finset.antidiagonal n, coeff p.1 L * coeff p.2 B := by
  cases n with
  | zero =>
      have hn := congrArg (coeff 0) h
      rw [coeff_zero_X_mul, coeff_mul] at hn
      simpa only [Nat.cast_zero, mul_zero] using hn
  | succ n =>
      have hn := congrArg (coeff (n + 1)) h
      rw [coeff_succ_X_mul, coeff_derivative, coeff_mul] at hn
      simpa only [Nat.cast_add, Nat.cast_one] using hn

theorem nat_mul_coeff_eq_sum_range_of_X_mul_derivativeFun_eq_mul
    {L B : R⟦X⟧} (h : X * PowerSeries.derivative R L = L * B) (n : Nat) :
    (n : R) * coeff n L =
      ∑ i ∈ Finset.range (n + 1), coeff (n - i) L * coeff i B := by
  rw [mul_comm]
  rw [coeff_mul_nat_eq_sum_antidiagonal_of_X_mul_derivativeFun_eq_mul h n]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ coeff j L * coeff i B) n

theorem nat_mul_coeff_eq_sum_positive_of_X_mul_derivativeFun_eq_mul
    {L B : R⟦X⟧} (h : X * PowerSeries.derivative R L = L * B)
    (hB : constantCoeff B = 0) (n : Nat) :
    (n : R) * coeff n L =
      ∑ i ∈ Finset.range n, coeff (n - (i + 1)) L * coeff (i + 1) B := by
  rw [nat_mul_coeff_eq_sum_range_of_X_mul_derivativeFun_eq_mul h n,
    Finset.sum_range_succ']
  simp only [coeff_zero_eq_constantCoeff_apply, hB, mul_zero, add_zero]

theorem coeff_logDerivative_eq_of_coeff_eq_up_to
    [IsLeftCancelAdd R] {L A B C : R⟦X⟧} {N : Nat}
    (hLB : X * PowerSeries.derivative R L = L * B)
    (hAC : X * PowerSeries.derivative R A = A * C)
    (hB0 : constantCoeff B = 0) (hC0 : constantCoeff C = 0)
    (hL0 : coeff 0 L = 1)
    (hcoeff : ∀ j, j ≤ N → coeff j L = coeff j A)
    {n : Nat} (hnN : n ≤ N) :
    coeff n B = coeff n C := by
  have hA0 : coeff 0 A = 1 := by
    rw [← hcoeff 0 (Nat.zero_le N)]
    exact hL0
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp only [coeff_zero_eq_constantCoeff_apply, hB0, hC0]
      | succ k =>
          have hrecL :=
            nat_mul_coeff_eq_sum_positive_of_X_mul_derivativeFun_eq_mul
              hLB hB0 (k + 1)
          have hrecA :=
            nat_mul_coeff_eq_sum_positive_of_X_mul_derivativeFun_eq_mul
              hAC hC0 (k + 1)
          have hsums :
              (∑ i ∈ Finset.range (k + 1),
                coeff (k + 1 - (i + 1)) L * coeff (i + 1) B) =
              ∑ i ∈ Finset.range (k + 1),
                coeff (k + 1 - (i + 1)) A * coeff (i + 1) C := by
            rw [← hrecL, ← hrecA, hcoeff (k + 1) hnN]
          rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsums
          have hprevious :
              (∑ i ∈ Finset.range k,
                coeff (k + 1 - (i + 1)) L * coeff (i + 1) B) =
              ∑ i ∈ Finset.range k,
                coeff (k + 1 - (i + 1)) A * coeff (i + 1) C := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hcoeff _ (Nat.le_trans (Nat.sub_le _ _) hnN)]
            rw [ih (i + 1)
              (by simp only [Finset.mem_range] at hi; omega)
              (by simp only [Finset.mem_range] at hi; omega)]
          rw [hprevious] at hsums
          simp only [Nat.sub_self, hL0, hA0, one_mul] at hsums
          exact add_left_cancel hsums

end RationalWeil

end Erdos387
