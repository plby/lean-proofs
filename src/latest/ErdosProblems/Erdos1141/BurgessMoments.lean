import ErdosProblems.Erdos1141.StepanovSqrt
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Arbitrary moments of shifted quadratic character sums
-/

namespace Pollack17.Burgess

open Polynomial
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def qchar (x : ZMod p) : ℝ := (quadraticChar (ZMod p) x : ℝ)

theorem qchar_prod {ι : Type*} [Fintype ι] (f : ι → ZMod p) :
    qchar (∏ i, f i) = ∏ i, qchar (f i) := by
  simp [qchar, map_prod]

noncomputable def shiftPolynomial {n : ℕ} (v : Fin n → ZMod p) : (ZMod p)[X] :=
  ∏ i : Fin n, (X + C (v i))

theorem shiftPolynomial_ne_zero {n : ℕ} (v : Fin n → ZMod p) : shiftPolynomial v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Polynomial.X_add_C_ne_zero (v i)

theorem shiftPolynomial_natDegree {n : ℕ} (v : Fin n → ZMod p) :
    (shiftPolynomial v).natDegree = n := by
  rw [shiftPolynomial, Polynomial.natDegree_prod]
  · simp
  · intro i _
    exact Polynomial.X_add_C_ne_zero (v i)

theorem shiftPolynomial_simple_root {n : ℕ} (v : Fin n → ZMod p) (i : Fin n)
    (hsingle : ∀ j : Fin n, j ≠ i → v j ≠ v i) :
    (shiftPolynomial v).rootMultiplicity (-v i) = 1 := by
  classical
  let Q : (ZMod p)[X] := ∏ j ∈ Finset.univ.erase i, (X + C (v j))
  have hfactor : shiftPolynomial v = (X + C (v i)) * Q := by
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hQeval : Q.eval (-v i) ≠ 0 := by
    simp only [Q, eval_prod, eval_add, eval_X, eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hne := hsingle j (Finset.mem_erase.mp hj).1
    simpa only [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hne
  have hQroot : Q.rootMultiplicity (-v i) = 0 := Polynomial.rootMultiplicity_eq_zero hQeval
  have hmul : (X + C (v i)) * Q ≠ 0 := hfactor ▸ shiftPolynomial_ne_zero v
  rw [hfactor, Polynomial.rootMultiplicity_mul hmul, hQroot, add_zero]
  simpa only [map_neg, sub_neg_eq_add] using
    (Polynomial.rootMultiplicity_X_sub_C_self (x := -v i))

theorem correlation_le_of_singleton {n : ℕ} (v : Fin n → ZMod p)
    (hsingle : ∃ i : Fin n, ∀ j : Fin n, j ≠ i → v j ≠ v i) :
    |∑ x : ZMod p, qchar (∏ i : Fin n, (x + v i))| ≤
      (Stepanov.simpleRootConstant n : ℝ) * Real.sqrt p := by
  obtain ⟨i, hi⟩ := hsingle
  have h := Stepanov.abs_polynomialCharacterSum_le_sqrt (shiftPolynomial v)
    (shiftPolynomial_ne_zero v) (shiftPolynomial_simple_root v i hi)
  rw [shiftPolynomial_natDegree] at h
  simpa only [Stepanov.polynomialCharacterSum, shiftPolynomial, eval_prod,
    eval_add, eval_X, eval_C, qchar] using h

noncomputable def shiftSum (V : Finset (ZMod p)) (x : ZMod p) : ℝ :=
  ∑ v ∈ V, qchar (x + v)

/-- The complete moment expansion for every natural moment order. -/
theorem shiftSum_moment_expansion (V : Finset (ZMod p)) (n : ℕ) :
    (∑ x : ZMod p, shiftSum V x ^ n) =
      ∑ v : Fin n → V, ∑ x : ZMod p,
        qchar (∏ i : Fin n, (x + (v i : ZMod p))) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [shiftSum, ← Finset.sum_attach, Finset.attach_eq_univ, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro v _
  exact (qchar_prod (fun i : Fin n => x + (v i : ZMod p))).symm

end Pollack17.Burgess
