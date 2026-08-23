/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Linear independence of shifted polynomials

This module proves the characteristic-zero form of van der Poorten--Loxton,
Lemma 7.  If `P` has positive degree `m` and `t ≤ m`, then

`P(X), P(X+1), ..., P(X+t), 1, X, ..., X^(m-t-1)`

is linearly independent.  The characteristic-zero hypothesis is necessary:
over `ZMod 2`, the polynomials `X ^ 2`, `(X + 1) ^ 2`, and `1` are dependent.
-/

open scoped BigOperators Matrix Polynomial

noncomputable section

namespace Erdos240

open Polynomial

/-- The shifted-polynomial family from van der Poorten--Loxton, Lemma 7. -/
def shiftedPolynomialFamily {K : Type*} [Field K] (P : K[X]) (m t : ℕ) :
    Fin (t + 1) ⊕ Fin (m - t) → K[X]
  | Sum.inl i => P.taylor (i : K)
  | Sum.inr j => X ^ (j : ℕ)

private theorem hasseDeriv_top_sub_ne_zero
    {K : Type*} [Field K] [CharZero K] (P : K[X]) {m j : ℕ}
    (hP : P ≠ 0) (hm : P.natDegree = m) (hj : j ≤ m) :
    P.hasseDeriv (m - j) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun Q : K[X] => Q.coeff j) hzero
  rw [hasseDeriv_coeff, coeff_zero] at hcoeff
  have hadd : j + (m - j) = m := Nat.add_sub_of_le hj
  have hcoeffm : P.coeff m = P.leadingCoeff := by
    rw [← hm, coeff_natDegree]
  rw [hadd, hcoeffm] at hcoeff
  have hchooseNat : 0 < m.choose (m - j) := Nat.choose_pos (Nat.sub_le m j)
  have hchoose : ((m.choose (m - j) : ℕ) : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hchooseNat.ne'
  exact mul_ne_zero hchoose (leadingCoeff_ne_zero.mpr hP) hcoeff

private theorem normalized_hasseDeriv_data
    {K : Type*} [Field K] [CharZero K] (P : K[X]) {m t : ℕ}
    (hP : P ≠ 0) (hm : P.natDegree = m) (ht : t ≤ m) :
    let q : Fin (t + 1) → K[X] := fun j => P.hasseDeriv (m - (j : ℕ))
    let r : Fin (t + 1) → K[X] :=
      fun j => C ((q j).leadingCoeff⁻¹) * q j
    (∀ j, (r j).natDegree = (j : ℕ)) ∧ ∀ j, (r j).Monic := by
  have hjm (j : Fin (t + 1)) : (j : ℕ) ≤ m :=
    (Nat.le_of_lt_succ j.isLt).trans ht
  have hq0 (j : Fin (t + 1)) : P.hasseDeriv (m - (j : ℕ)) ≠ 0 :=
    hasseDeriv_top_sub_ne_zero P hP hm (hjm j)
  have hqdeg (j : Fin (t + 1)) :
      (P.hasseDeriv (m - (j : ℕ))).natDegree = (j : ℕ) := by
    rw [natDegree_hasseDeriv, hm]
    omega
  constructor
  · intro j
    rw [natDegree_C_mul (inv_ne_zero (leadingCoeff_ne_zero.mpr (hq0 j))), hqdeg]
  · intro j
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr (hq0 j))

/-- If a linear combination of the shifted copies of `P` and the indicated
low monomials vanishes, all its coefficients vanish.  This coefficient form
is convenient in determinant arguments. -/
theorem shiftedPolynomial_relation
    {K : Type*} [Field K] [CharZero K] (P : K[X]) {m t : ℕ}
    (hm_pos : 0 < m) (hm : P.natDegree = m) (ht : t ≤ m)
    (a : Fin (t + 1) → K) (b : Fin (m - t) → K)
    (hrel : (∑ i, a i • P.taylor (i : K)) +
      ∑ j, b j • X ^ (j : ℕ) = 0) :
    a = 0 ∧ b = 0 := by
  have hP : P ≠ 0 := by
    intro h
    subst P
    simp at hm
    omega
  let q : Fin (t + 1) → K[X] := fun j => P.hasseDeriv (m - (j : ℕ))
  let r : Fin (t + 1) → K[X] := fun j => C ((q j).leadingCoeff⁻¹) * q j
  have hr := normalized_hasseDeriv_data P hP hm ht
  dsimp only at hr
  change (∀ j, (r j).natDegree = (j : ℕ)) ∧ ∀ j, (r j).Monic at hr
  have hcast : Function.Injective (fun i : Fin (t + 1) => (i : K)) := by
    intro i j hij
    apply Fin.ext
    exact Nat.cast_injective hij
  let M : Matrix (Fin (t + 1)) (Fin (t + 1)) K :=
    Matrix.of fun i j => (r j).eval (i : K)
  have hdet : M.det ≠ 0 := by
    change (Matrix.of fun (i j : Fin (t + 1)) => (r j).eval (i : K)).det ≠ 0
    rw [← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun i : Fin (t + 1) => (i : K)) r hr.1 hr.2]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hcast
  have hhigh (j : Fin (t + 1)) :
      ∑ i, a i * (q j).eval (i : K) = 0 := by
    have hc := congrArg (lcoeff K (m - (j : ℕ))) hrel
    simp only [map_add, map_sum, map_zero, lcoeff_apply, coeff_smul, smul_eq_mul] at hc
    simp_rw [taylor_coeff] at hc
    change (∑ i, a i * (q j).eval (i : K)) +
      (∑ x, b x * (X ^ (x : ℕ) : K[X]).coeff (m - (j : ℕ))) = 0 at hc
    have hlow : ∑ x, b x * (X ^ (x : ℕ) : K[X]).coeff (m - (j : ℕ)) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [coeff_X_pow, if_neg, mul_zero]
      have hx : (x : ℕ) < m - t := x.isLt
      have hj : (j : ℕ) ≤ t := Nat.le_of_lt_succ j.isLt
      omega
    rw [hlow, add_zero] at hc
    exact hc
  have hvec : a ᵥ* M = 0 := by
    funext j
    simp only [Matrix.vecMul, dotProduct, M, Matrix.of_apply, Pi.zero_apply]
    simp only [r, eval_mul, eval_C]
    calc
      _ = (q j).leadingCoeff⁻¹ * ∑ i, a i * (q j).eval (i : K) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ac_rfl
      _ = 0 := by rw [hhigh j, mul_zero]
  have ha : a = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  refine ⟨ha, ?_⟩
  funext j
  have hc := congrArg (lcoeff K (j : ℕ)) hrel
  simp only [map_add, map_sum, map_zero, lcoeff_apply, coeff_smul, smul_eq_mul,
    ha, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] at hc
  have hval (x : Fin (m - t)) : ((j : ℕ) = (x : ℕ)) ↔ x = j := by
    rw [Fin.ext_iff]
    exact eq_comm
  simp only [coeff_X_pow, hval, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hc
  exact hc

/-- For a positive-degree polynomial `P` of degree `m`, its shifts through
`t` together with the monomials of degree below `m - t` are linearly
independent. -/
theorem linearIndependent_shiftedPolynomialFamily
    {K : Type*} [Field K] [CharZero K] (P : K[X]) {m t : ℕ}
    (hm_pos : 0 < m) (hm : P.natDegree = m) (ht : t ≤ m) :
    LinearIndependent K (shiftedPolynomialFamily P m t) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc z
  let a : Fin (t + 1) → K := fun i => c (Sum.inl i)
  let b : Fin (m - t) → K := fun j => c (Sum.inr j)
  have hsplit : (∑ i, a i • P.taylor (i : K)) +
      ∑ j, b j • X ^ (j : ℕ) = 0 := by
    simpa only [Fintype.sum_sum_type, shiftedPolynomialFamily, a, b] using hc
  have hz := shiftedPolynomial_relation P hm_pos hm ht a b hsplit
  cases z with
  | inl i => exact congrFun hz.1 i
  | inr j => exact congrFun hz.2 j

end Erdos240
