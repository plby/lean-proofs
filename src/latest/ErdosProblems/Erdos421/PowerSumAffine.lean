import ErdosProblems.Erdos421.PowerSumFibers
import ErdosProblems.Erdos421.TriangularSums

/-! # Affine invariance of complete power-sum equations -/

namespace Erdos421

open Polynomial

section CommRing

variable {R : Type*} [CommRing R] {s n : ℕ}

theorem polynomial_sums_eq_of_powerSumVector_eq (x y : Fin s → R)
    (hs : powerSumVector n x = powerSumVector n y) (P : R[X]) (hP : P.natDegree ≤ n) :
    (∑ i : Fin s, P.eval (x i)) = ∑ i : Fin s, P.eval (y i) := by
  rw [sum_eval_eq_sum_coeff_power x P hP, sum_eval_eq_sum_coeff_power y P hP]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hj0 : j = 0
  · simp only [hj0, pow_zero]
  · rw [(powerSumVector_eq_iff x y).mp hs j (Nat.pos_of_ne_zero hj0)
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]

theorem powerSumVector_add_const_eq (x y : Fin s → R)
    (hs : powerSumVector n x = powerSumVector n y) (b : R) :
    powerSumVector n (fun i ↦ x i + b) = powerSumVector n (fun i ↦ y i + b) := by
  nontriviality R
  funext j
  have hd : ((X + C b) ^ ((j : ℕ) + 1)).natDegree ≤ n := by
    apply Polynomial.natDegree_pow_le.trans
    rw [Polynomial.natDegree_X_add_C, mul_one]
    exact Nat.succ_le_of_lt j.isLt
  simpa only [powerSumVector, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C] using
    polynomial_sums_eq_of_powerSumVector_eq x y hs ((X + C b) ^ ((j : ℕ) + 1)) hd

theorem powerSumVector_add_const_eq_iff (x y : Fin s → R) (b : R) :
    powerSumVector n (fun i ↦ x i + b) = powerSumVector n (fun i ↦ y i + b) ↔
      powerSumVector n x = powerSumVector n y := by
  constructor
  · intro h
    simpa only [add_neg_cancel_right] using
      powerSumVector_add_const_eq (fun i ↦ x i + b) (fun i ↦ y i + b) h (-b)
  · intro h
    exact powerSumVector_add_const_eq x y h b

theorem powerSumVector_mul_const (x : Fin s → R) (a : R) (j : Fin n) :
    powerSumVector n (fun i ↦ a * x i) j = a ^ ((j : ℕ) + 1) * powerSumVector n x j := by
  simp only [powerSumVector, mul_pow, Finset.mul_sum]

end CommRing

theorem powerSumVector_affine_eq_iff {R : Type*} [CommRing R] [IsDomain R]
    {s n : ℕ} (x y : Fin s → R) (a b : R) (ha : a ≠ 0) :
    powerSumVector n (fun i ↦ a * x i + b) = powerSumVector n (fun i ↦ a * y i + b) ↔
      powerSumVector n x = powerSumVector n y := by
  rw [powerSumVector_add_const_eq_iff]
  constructor
  · intro h
    funext j
    have he := congrFun h j
    simp only [powerSumVector_mul_const] at he
    exact mul_left_cancel₀ (pow_ne_zero _ ha) he
  · intro h
    funext j
    rw [powerSumVector_mul_const, powerSumVector_mul_const, h]

end Erdos421
