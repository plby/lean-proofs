/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Matrix.Mul

/-!
# A confluent Vandermonde zero lemma

The theorem below is the polynomial form of injectivity of a confluent
Vandermonde matrix. At the node `x i` we prescribe `m i` consecutive Hasse
derivatives. A polynomial of degree strictly smaller than the total number of
conditions is determined by those values.
-/

open scoped Function Matrix

namespace Erdos240.Multiplicity

open Finset Polynomial

variable {K ι : Type*} [Field K] [Fintype ι]

/-- Vanishing of the first `m i` Hasse derivatives at pairwise distinct nodes,
with total multiplicity greater than the degree, forces a polynomial to vanish.

This is the zero lemma underlying the nonsingularity of the confluent
Vandermonde matrix. It is slightly stronger than the form needed for
exponential polynomials: the nodes need not be nonzero. -/
theorem eq_zero_of_hasseDeriv_eval_eq_zero_of_natDegree_lt_sum
    (x : ι → K) (m : ι → ℕ) (P : K[X])
    (hx : Function.Injective x)
    (hdeg : P.natDegree < ∑ i, m i)
    (hzero : ∀ i k, k < m i → (hasseDeriv k P).eval (x i) = 0) :
    P = 0 := by
  classical
  have hdiv : ∀ i, (X - C (x i)) ^ m i ∣ P := by
    intro i
    rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
    intro k hk
    rw [← taylor_apply]
    exact taylor_coeff (x i) P k |>.trans (hzero i k hk)
  have hcop : Pairwise (IsCoprime on fun i ↦ (X - C (x i)) ^ m i) := by
    intro i j hij
    exact (pairwise_coprime_X_sub_C hx hij).pow
  have hprod : (∏ i, (X - C (x i)) ^ m i) ∣ P :=
    Fintype.prod_dvd_of_coprime hcop hdiv
  have hprod_degree : (∏ i, (X - C (x i)) ^ m i).natDegree = ∑ i, m i := by
    rw [show (∏ i, (X - C (x i)) ^ m i) =
      ∏ i ∈ (univ : Finset ι), (X - C (x i)) ^ m i by simp]
    rw [natDegree_prod_of_monic]
    · simp [natDegree_pow]
    · intro i _
      exact (monic_X_sub_C (x i)).pow (m i)
  by_contra hP
  have := natDegree_le_of_dvd hprod hP
  rw [hprod_degree] at this
  exact (Nat.not_le_of_lt hdeg) this

/-- The same zero lemma with the nodes presented as units. This is the form
for distinct nonzero bases of an exponential polynomial. -/
theorem eq_zero_of_hasseDeriv_eval_units_eq_zero_of_natDegree_lt_sum
    (x : ι → Kˣ) (m : ι → ℕ) (P : K[X])
    (hx : Function.Injective x)
    (hdeg : P.natDegree < ∑ i, m i)
    (hzero : ∀ i k, k < m i → (hasseDeriv k P).eval (x i : K) = 0) :
    P = 0 := by
  apply eq_zero_of_hasseDeriv_eval_eq_zero_of_natDegree_lt_sum
      (fun i ↦ (x i : K)) m P
  · intro i j hij
    apply hx
    exact Units.ext hij
  · exact hdeg
  · exact hzero

/-- The rectangular confluent Vandermonde matrix with columns indexed by
monomials of degree below `N`. Its row `(i,k)` records the value at `x i` of
the `k`th Hasse derivative of that monomial. -/
def confluentVandermonde (x : ι → K) (m : ι → ℕ) (N : ℕ) :
    Matrix (Σ i, Fin (m i)) (Fin N) K :=
  fun ik j ↦ (j.val.choose ik.2.val : K) * x ik.1 ^ (j.val - ik.2.val)

omit [Fintype ι] in
@[simp]
theorem confluentVandermonde_apply (x : ι → K) (m : ι → ℕ) (N : ℕ)
    (ik : Σ i, Fin (m i)) (j : Fin N) :
    confluentVandermonde x m N ik j =
      (j.val.choose ik.2.val : K) * x ik.1 ^ (j.val - ik.2.val) :=
  rfl

/-- A square confluent Vandermonde system at distinct nodes has trivial
kernel. The equality `N = ∑ i, m i` says that the number of monomial
coefficients is exactly the number of derivative conditions. -/
theorem confluentVandermonde_mulVec_eq_zero
    (x : ι → K) (m : ι → ℕ) (N : ℕ)
    (hx : Function.Injective x) (hN : N = ∑ i, m i)
    (c : Fin N → K) (hc : confluentVandermonde x m N *ᵥ c = 0) :
    c = 0 := by
  classical
  by_cases hN0 : N = 0
  · apply funext
    intro j
    exact Fin.elim0 (hN0 ▸ j)
  let P : K[X] := ofFn N c
  have hPdeg : P.natDegree < ∑ i, m i := by
    rw [← hN]
    exact ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr hN0) c
  have hPzero : ∀ i k, k < m i → (hasseDeriv k P).eval (x i) = 0 := by
    intro i k hk
    have hrow := congr_fun hc (Sigma.mk i ⟨k, hk⟩)
    simp only [Pi.zero_apply] at hrow
    dsimp [P]
    rw [ofFn_eq_sum_monomial]
    simp only [map_sum, eval_finsetSum, hasseDeriv_monomial, eval_monomial]
    rw [show ∑ j : Fin N,
          (j.val.choose k : K) * c j * x i ^ (j.val - k) =
        (confluentVandermonde x m N *ᵥ c) ⟨i, ⟨k, hk⟩⟩ by
      simp only [Matrix.mulVec, dotProduct, confluentVandermonde_apply]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    exact hrow
  have hP : P = 0 :=
    eq_zero_of_hasseDeriv_eval_eq_zero_of_natDegree_lt_sum x m P hx hPdeg hPzero
  exact (injective_ofFn N) (hP.trans (ofFn_zero N).symm)

/-- The explicit matrix-kernel form for distinct nonzero bases. -/
theorem confluentVandermonde_units_mulVec_eq_zero
    (x : ι → Kˣ) (m : ι → ℕ) (N : ℕ)
    (hx : Function.Injective x) (hN : N = ∑ i, m i)
    (c : Fin N → K)
    (hc : confluentVandermonde (fun i ↦ (x i : K)) m N *ᵥ c = 0) :
    c = 0 := by
  apply confluentVandermonde_mulVec_eq_zero (fun i ↦ (x i : K)) m N
  · intro i j hij
    apply hx
    exact Units.ext hij
  · exact hN
  · exact hc

end Erdos240.Multiplicity

#print axioms Erdos240.Multiplicity.eq_zero_of_hasseDeriv_eval_eq_zero_of_natDegree_lt_sum
#print axioms Erdos240.Multiplicity.confluentVandermonde_units_mulVec_eq_zero
