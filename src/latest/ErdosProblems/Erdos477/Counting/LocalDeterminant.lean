/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A two-variable local polynomial determinant estimate for Erdős Problem 477.
Formal author: Codex.

This is a proved arithmetic ingredient for the determinant method, not the
surface covering theorem. Applying it to a surface will additionally require
local polynomial expansions in its two free coordinates.
-/

import ErdosProblems.Erdos477.Counting.Determinant
import ErdosProblems.Erdos477.Counting.Monomials

namespace Erdos477.Counting

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The integral exponent furnished by a monomial threshold. -/
def localExponent (s m : ℕ) : ℕ := m * s - m * (m + 1) * (m + 2) / 6

/-- Evaluation determinants for polynomials in two variables over any
commutative ring, at points in `(p) × (p)`, have a large common power divisor. -/
theorem pow_dvd_polynomial_eval_det {s : ℕ} (p : R)
    (F : Fin s → MvPolynomial (Fin 2) R) (x y : Fin s → R) (m : ℕ) :
    p ^ localExponent s m ∣
      Matrix.det (Matrix.of fun i j => MvPolynomial.eval ![p * x j, p * y j] (F i)) := by
  classical
  let S : Finset (Fin 2 →₀ ℕ) := Finset.univ.biUnion (fun i => (F i).support)
  let e : S → ℕ × ℕ := fun k => (k.val 0, k.val 1)
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    fin_cases k
    · exact congrArg Prod.fst hab
    · exact congrArg Prod.snd hab
  have heval (i j : Fin s) :
      MvPolynomial.eval ![p * x j, p * y j] (F i) =
      ∑ k : S, (F i).coeff k.val *
        ((p * x j) ^ (e k).1 * (p * y j) ^ (e k).2) := by
    rw [MvPolynomial.eval_eq']
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    change (∑ k ∈ (F i).support, (F i).coeff k *
      ((p * x j) ^ k 0 * (p * y j) ^ k 1)) =
      ∑ k : S, (F i).coeff k.val *
        ((p * x j) ^ k.val 0 * (p * y j) ^ k.val 1)
    calc
      _ = ∑ k ∈ S, (F i).coeff k * ((p * x j) ^ k 0 * (p * y j) ^ k 1) := by
        apply Finset.sum_subset
        · intro k hk
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hk⟩
        · intro k _ hk
          have hzero : (F i).coeff k = 0 := by
            simpa only [MvPolynomial.mem_support_iff, not_not] using hk
          rw [hzero, zero_mul]
      _ = _ := (Finset.sum_coe_sort S (fun k =>
        (F i).coeff k * ((p * x j) ^ k 0 * (p * y j) ^ k 1))).symm
  simp_rw [heval]
  apply pow_dvd_det_bivariate_expansion p e he (fun i k => (F i).coeff k.val) x y
  intro f hf
  simpa only [localExponent, Fintype.card_fin] using sum_weights_injective_lower_bound f hf m

/-- The same bound holds in an arbitrary integral residue class. -/
theorem pow_dvd_polynomial_eval_det_translate {s : ℕ} (p a b : R)
    (F : Fin s → MvPolynomial (Fin 2) R) (x y : Fin s → R) (m : ℕ) :
    p ^ localExponent s m ∣ Matrix.det (Matrix.of fun i j =>
      MvPolynomial.eval ![a + p * x j, b + p * y j] (F i)) := by
  let G : Fin s → MvPolynomial (Fin 2) R := fun i =>
    MvPolynomial.eval₂ MvPolynomial.C
      ![MvPolynomial.C a + MvPolynomial.X 0, MvPolynomial.C b + MvPolynomial.X 1] (F i)
  have h := pow_dvd_polynomial_eval_det p G x y m
  have heval (i j : Fin s) :
      MvPolynomial.eval ![p * x j, p * y j] (G i) =
        MvPolynomial.eval ![a + p * x j, b + p * y j] (F i) := by
    dsimp only [G]
    rw [← MvPolynomial.eval_assoc]
    have hcoords :
        MvPolynomial.eval ![p * x j, p * y j] ∘
          ![MvPolynomial.C a + MvPolynomial.X 0, MvPolynomial.C b + MvPolynomial.X 1] =
        ![a + p * x j, b + p * y j] := by
      funext k
      fin_cases k <;> simp
    rw [hcoords]
  simpa only [heval] using h

/-- The determinant bound also applies when the entries are only congruent
to polynomial evaluations up to an order beyond the required exponent. -/
theorem pow_dvd_det_of_local_expansion {s : ℕ} (p : R) (A : Matrix (Fin s) (Fin s) R)
    (F : Fin s → MvPolynomial (Fin 2) R) (x y : Fin s → R) (m N : ℕ)
    (hN : localExponent s m ≤ N)
    (happrox : ∀ i j, p ^ N ∣ A i j - MvPolynomial.eval ![p * x j, p * y j] (F i)) :
    p ^ localExponent s m ∣ A.det := by
  apply pow_dvd_det_of_approximation p (localExponent s m) N hN A
    (Matrix.of fun i j => MvPolynomial.eval ![p * x j, p * y j] (F i))
  · exact happrox
  · exact pow_dvd_polynomial_eval_det p F x y m

#print axioms pow_dvd_polynomial_eval_det
-- 'Erdos477.Counting.pow_dvd_polynomial_eval_det' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
