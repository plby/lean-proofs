/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.ShiftedPolynomial
import ErdosProblems.Erdos240.Multiplicity
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The Lemma 7 zero-count contradiction

This module joins the linear independence of the shifted-polynomial family to
the Hasse-derivative multiplicity bound.  It is the generic algebraic endpoint
of the van der Poorten--Loxton induction: a nonzero coefficient vector cannot
produce a polynomial of degree at most `m` with more than `m` zeros counted
with multiplicity.
-/

open scoped BigOperators Polynomial

noncomputable section

namespace Erdos240

open Polynomial

/-- The linear combination of the shifted-polynomial family attached to a
coefficient vector. -/
def shiftedPolynomialCombination {K : Type*} [Field K]
    (P : K[X]) (m t : ℕ)
    (c : Fin (t + 1) ⊕ Fin (m - t) → K) : K[X] :=
  ∑ z, c z • shiftedPolynomialFamily P m t z

/-- Every member of the shifted-polynomial family has degree at most `m`.
For the shifted copies this follows from invariance of degree under Taylor
translation; for the low monomials it follows from their index bound. -/
theorem natDegree_shiftedPolynomialFamily_le
    {K : Type*} [Field K] (P : K[X]) {m t : ℕ}
    (hm : P.natDegree = m)
    (z : Fin (t + 1) ⊕ Fin (m - t)) :
    (shiftedPolynomialFamily P m t z).natDegree ≤ m := by
  cases z with
  | inl i =>
      simp only [shiftedPolynomialFamily, natDegree_taylor, hm, le_refl]
  | inr j =>
      simp only [shiftedPolynomialFamily, natDegree_X_pow]
      exact (Nat.le_of_lt j.isLt).trans (Nat.sub_le m t)

/-- A linear combination of the Lemma 7 family still has degree at most
`m`, independently of its coefficients. -/
theorem natDegree_shiftedPolynomialCombination_le
    {K : Type*} [Field K] (P : K[X]) {m t : ℕ}
    (hm : P.natDegree = m)
    (c : Fin (t + 1) ⊕ Fin (m - t) → K) :
    (shiftedPolynomialCombination P m t c).natDegree ≤ m := by
  classical
  unfold shiftedPolynomialCombination
  apply natDegree_sum_le_of_forall_le (Finset.univ)
  intro z _
  exact (natDegree_smul_le (c z) _).trans
    (natDegree_shiftedPolynomialFamily_le P hm z)

/-- If a shifted-family combination has more zeros counted with Hasse
multiplicity than its degree bound, then every coefficient is zero.  This is
the coefficient-level form of the final Lemma 7 contradiction. -/
theorem shiftedPolynomialCombination_eq_zero_coefficients_of_hasseDeriv
    {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    (P : K[X]) {m t : ℕ}
    (hm_pos : 0 < m) (hm : P.natDegree = m) (ht : t ≤ m)
    (x : ι → K) (multiplicity : ι → ℕ)
    (hx : Function.Injective x)
    (c : Fin (t + 1) ⊕ Fin (m - t) → K)
    (hcount : m < ∑ i, multiplicity i)
    (hzero : ∀ i k, k < multiplicity i →
      (hasseDeriv k (shiftedPolynomialCombination P m t c)).eval (x i) = 0) :
    c = 0 := by
  have hdegree : (shiftedPolynomialCombination P m t c).natDegree <
      ∑ i, multiplicity i :=
    (natDegree_shiftedPolynomialCombination_le P hm c).trans_lt hcount
  have hpoly : shiftedPolynomialCombination P m t c = 0 :=
    Multiplicity.eq_zero_of_hasseDeriv_eval_eq_zero_of_natDegree_lt_sum
      x multiplicity _ hx hdegree hzero
  have hlin := linearIndependent_shiftedPolynomialFamily P hm_pos hm ht
  apply funext
  exact Fintype.linearIndependent_iff.mp hlin c hpoly

/-- Constant-multiplicity specialization.  The total number of vanishing
conditions is `Fintype.card ι * r`. -/
theorem shiftedPolynomialCombination_eq_zero_coefficients_of_hasseDeriv_const
    {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    (P : K[X]) {m t r : ℕ}
    (hm_pos : 0 < m) (hm : P.natDegree = m) (ht : t ≤ m)
    (x : ι → K) (hx : Function.Injective x)
    (c : Fin (t + 1) ⊕ Fin (m - t) → K)
    (hcount : m < Fintype.card ι * r)
    (hzero : ∀ i k, k < r →
      (hasseDeriv k (shiftedPolynomialCombination P m t c)).eval (x i) = 0) :
    c = 0 := by
  apply shiftedPolynomialCombination_eq_zero_coefficients_of_hasseDeriv
      P hm_pos hm ht x (fun _ ↦ r) hx c
  · simpa using hcount
  · exact hzero

/-- Contrapositive form used directly in a final zero-count argument: a
nonzero coefficient vector supplies a node and an allowed Hasse derivative
whose value is nonzero. -/
theorem exists_hasseDeriv_shiftedPolynomialCombination_ne_zero
    {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    (P : K[X]) {m t : ℕ}
    (hm_pos : 0 < m) (hm : P.natDegree = m) (ht : t ≤ m)
    (x : ι → K) (multiplicity : ι → ℕ)
    (hx : Function.Injective x)
    (c : Fin (t + 1) ⊕ Fin (m - t) → K) (hc : c ≠ 0)
    (hcount : m < ∑ i, multiplicity i) :
    ∃ i k, k < multiplicity i ∧
      (hasseDeriv k (shiftedPolynomialCombination P m t c)).eval (x i) ≠ 0 := by
  by_contra hnone
  apply hc
  apply shiftedPolynomialCombination_eq_zero_coefficients_of_hasseDeriv
      P hm_pos hm ht x multiplicity hx c hcount
  intro i k hk
  by_contra hne
  exact hnone ⟨i, k, hk, hne⟩

/-- Split-coefficient version matching the traditional statement of Lemma 7.
It avoids repackaging the coefficients into the sum type at call sites. -/
theorem shiftedPolynomial_relation_of_hasseDeriv
    {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
    (P : K[X]) {m t : ℕ}
    (hm_pos : 0 < m) (hm : P.natDegree = m) (ht : t ≤ m)
    (x : ι → K) (multiplicity : ι → ℕ)
    (hx : Function.Injective x)
    (a : Fin (t + 1) → K) (b : Fin (m - t) → K)
    (hcount : m < ∑ i, multiplicity i)
    (hzero : ∀ i k, k < multiplicity i →
      (hasseDeriv k ((∑ j, a j • P.taylor (j : K)) +
        ∑ j, b j • X ^ (j : ℕ))).eval (x i) = 0) :
    a = 0 ∧ b = 0 := by
  let c : Fin (t + 1) ⊕ Fin (m - t) → K := Sum.elim a b
  have hcomb : shiftedPolynomialCombination P m t c =
      (∑ j, a j • P.taylor (j : K)) + ∑ j, b j • X ^ (j : ℕ) := by
    simp only [shiftedPolynomialCombination, Fintype.sum_sum_type,
      shiftedPolynomialFamily, c, Sum.elim_inl, Sum.elim_inr]
  have hc : c = 0 :=
    shiftedPolynomialCombination_eq_zero_coefficients_of_hasseDeriv
      P hm_pos hm ht x multiplicity hx c hcount (by
        intro i k hk
        rw [hcomb]
        exact hzero i k hk)
  constructor
  · funext i
    exact congrFun hc (Sum.inl i)
  · funext j
    exact congrFun hc (Sum.inr j)

end Erdos240

#print axioms Erdos240.shiftedPolynomialCombination_eq_zero_coefficients_of_hasseDeriv
#print axioms Erdos240.exists_hasseDeriv_shiftedPolynomialCombination_ne_zero
#print axioms Erdos240.shiftedPolynomial_relation_of_hasseDeriv
