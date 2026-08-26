/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The six coefficient coordinates of an affine plane quadratic.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Geometry

open scoped BigOperators

noncomputable def planeExponent (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

@[simp] lemma planeExponent_zero (a b : ℕ) : planeExponent a b 0 = a := by
  simp [planeExponent]

@[simp] lemma planeExponent_one (a b : ℕ) : planeExponent a b 1 = b := by
  simp [planeExponent]

noncomputable def quadraticExponent (i : Fin 6) : Fin 2 →₀ ℕ :=
  ![planeExponent 2 0, planeExponent 1 1, planeExponent 0 2,
    planeExponent 1 0, planeExponent 0 1, planeExponent 0 0] i

lemma quadraticExponent_injective : Function.Injective quadraticExponent := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [quadraticExponent, Finsupp.ext_iff, Fin.forall_fin_two]

lemma exists_quadraticExponent (m : Fin 2 →₀ ℕ) (hm : m 0 + m 1 ≤ 2) :
    ∃ i : Fin 6, quadraticExponent i = m := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false]
  simp only [quadraticExponent, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finsupp.ext_iff, Fin.forall_fin_two, planeExponent_zero, planeExponent_one]
  omega

variable {R : Type*} [CommRing R]

noncomputable def planeQuadratic (a : Fin 6 → R) : MvPolynomial (Fin 2) R :=
  ∑ i, MvPolynomial.monomial (quadraticExponent i) (a i)

lemma coeff_planeQuadratic (a : Fin 6 → R) (i : Fin 6) :
    (planeQuadratic a).coeff (quadraticExponent i) = a i := by
  classical
  simp [planeQuadratic, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    quadraticExponent_injective.eq_iff]

lemma totalDegree_planeQuadratic (a : Fin 6 → R) : (planeQuadratic a).totalDegree ≤ 2 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  change (quadraticExponent i).sum (fun _ n => n) ≤ 2
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  fin_cases i <;> norm_num [quadraticExponent]

theorem eq_planeQuadratic_of_totalDegree_le (P : MvPolynomial (Fin 2) R)
    (hP : P.totalDegree ≤ 2) :
    P = planeQuadratic (fun i => P.coeff (quadraticExponent i)) := by
  classical
  ext m
  by_cases hm : m 0 + m 1 ≤ 2
  · obtain ⟨i, rfl⟩ := exists_quadraticExponent m hm
    exact (coeff_planeQuadratic (fun j => P.coeff (quadraticExponent j)) i).symm
  · have hzero (Q : MvPolynomial (Fin 2) R) (hQ : Q.totalDegree ≤ 2) : Q.coeff m = 0 := by
      apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
      change Q.totalDegree < m.sum (fun _ n => n)
      rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
      omega
    rw [hzero P hP, hzero _ (totalDegree_planeQuadratic _)]

lemma eval_planeQuadratic (a : Fin 6 → R) (x y : R) :
    MvPolynomial.eval ![x, y] (planeQuadratic a) =
      a 0 * x ^ 2 + a 1 * x * y + a 2 * y ^ 2 + a 3 * x + a 4 * y + a 5 := by
  simp only [planeQuadratic, map_sum, MvPolynomial.eval_monomial]
  simp_rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp [Fin.sum_univ_succ, quadraticExponent, mul_assoc, add_assoc]

lemma planeQuadratic_eq (a : Fin 6 → R) :
    planeQuadratic a = MvPolynomial.C (a 0) * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.C (a 1) * MvPolynomial.X 0 * MvPolynomial.X 1 +
      MvPolynomial.C (a 2) * MvPolynomial.X 1 ^ 2 + MvPolynomial.C (a 3) * MvPolynomial.X 0 +
      MvPolynomial.C (a 4) * MvPolynomial.X 1 + MvPolynomial.C (a 5) := by
  simp only [planeQuadratic, MvPolynomial.monomial_eq]
  simp_rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp [Fin.sum_univ_succ, quadraticExponent, mul_assoc, add_assoc]

#print axioms eq_planeQuadratic_of_totalDegree_le
-- 'Erdos477.Geometry.eq_planeQuadratic_of_totalDegree_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
