/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Combining two-variable local expansions over several residue classes.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.LocalDeterminant
import ErdosProblems.Erdos477.Counting.ResidueMonomials

namespace Erdos477.Counting

open scoped BigOperators

variable {R κ : Type*} [CommRing R] [Fintype κ]

/-- Different residue classes may use different polynomial expansions.
Keeping a class label on each monomial gives a determinant divisor controlled
by the number of classes, without any assumption on their populations. -/
theorem pow_dvd_piecewise_polynomial_eval_det {s : ℕ} (p : R)
    (F : Fin s → κ → MvPolynomial (Fin 2) R) (g : Fin s → κ) (x y : Fin s → R) (m : ℕ) :
    p ^ residueExponent (Fintype.card κ) s m ∣ Matrix.det (Matrix.of fun i j =>
      MvPolynomial.eval ![p * x j, p * y j] (F i (g j))) := by
  classical
  let S : Finset (Fin 2 →₀ ℕ) :=
    Finset.univ.biUnion (fun k => Finset.univ.biUnion (fun i => (F i k).support))
  let e : κ × S → κ × (ℕ × ℕ) := fun k => (k.1, (k.2.val 0, k.2.val 1))
  have he : Function.Injective e := by
    intro a b hab
    refine Prod.ext ?_ ?_
    · exact congrArg (fun q : κ × (ℕ × ℕ) => q.1) hab
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    fin_cases k
    · exact congrArg (fun q => q.2.1) hab
    · exact congrArg (fun q => q.2.2) hab
  have heval (i : Fin s) (k : κ) (j : Fin s) :
      MvPolynomial.eval ![p * x j, p * y j] (F i k) =
      ∑ a : S, (F i k).coeff a.val *
        ((p * x j) ^ (a.val 0) * (p * y j) ^ (a.val 1)) := by
    rw [MvPolynomial.eval_eq']
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    calc
      _ = ∑ a ∈ S, (F i k).coeff a * ((p * x j) ^ a 0 * (p * y j) ^ a 1) := by
        apply Finset.sum_subset
        · intro a ha
          exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k,
            Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ha⟩⟩
        · intro a _ ha
          have hzero : (F i k).coeff a = 0 := by
            simpa only [MvPolynomial.mem_support_iff, not_not] using ha
          rw [hzero, zero_mul]
      _ = _ := (Finset.sum_coe_sort S (fun a =>
        (F i k).coeff a * ((p * x j) ^ a 0 * (p * y j) ^ a 1))).symm
  let C : Fin s → κ × S → R := fun i k => (F i k.1).coeff k.2.val
  let W : κ × S → Fin s → R := fun k j =>
    if g j = k.1 then x j ^ k.2.val 0 * y j ^ k.2.val 1 else 0
  have hentry (i j : Fin s) :
      (∑ k : κ × S, (C i k * p ^ ((e k).2.1 + (e k).2.2)) * W k j) =
        MvPolynomial.eval ![p * x j, p * y j] (F i (g j)) := by
    dsimp only [C, W, e]
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [heval]
    apply Finset.sum_congr rfl
    intro k _
    simp only [mul_pow, pow_add]
    ring
  have h := pow_dvd_det_weighted_sum p (fun k => (e k).2.1 + (e k).2.2) C W
    (residueExponent (Fintype.card κ) s m) (fun f hf => by
      simpa only [Function.comp_apply, Fintype.card_fin] using
        sum_labeled_weights_injective_lower_bound (e ∘ f) (he.comp hf) m)
  simpa only [hentry] using h

/-- Approximations on finitely many residue classes suffice to obtain the
same determinant divisor. -/
theorem pow_dvd_det_of_piecewise_expansion {s : ℕ} (p : R)
    (A : Matrix (Fin s) (Fin s) R) (F : Fin s → κ → MvPolynomial (Fin 2) R)
    (g : Fin s → κ) (x y : Fin s → R) (m N : ℕ)
    (hN : residueExponent (Fintype.card κ) s m ≤ N)
    (happrox : ∀ i j, p ^ N ∣ A i j -
      MvPolynomial.eval ![p * x j, p * y j] (F i (g j))) :
    p ^ residueExponent (Fintype.card κ) s m ∣ A.det := by
  apply pow_dvd_det_of_approximation p _ N hN A
    (Matrix.of fun i j => MvPolynomial.eval ![p * x j, p * y j] (F i (g j)))
  · exact happrox
  · exact pow_dvd_piecewise_polynomial_eval_det p F g x y m

#print axioms pow_dvd_piecewise_polynomial_eval_det
-- 'Erdos477.Counting.pow_dvd_piecewise_polynomial_eval_det' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
