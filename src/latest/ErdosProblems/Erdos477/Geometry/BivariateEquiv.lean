/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Connecting total degree of plane polynomials with the iterated-polynomial resultant.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.PlaneProjection

namespace Erdos477.Geometry

open scoped Polynomial

variable {R : Type*} [CommSemiring R]

lemma natDegree_uniqueAlgEquiv_le (P : MvPolynomial (Fin 1) R) :
    (MvPolynomial.uniqueAlgEquiv R (Fin 1) P).natDegree ≤ P.totalDegree := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  by_contra h
  have hm := MvPolynomial.mem_support_iff.mpr h
  have hd := MvPolynomial.le_totalDegree hm
  simp only [Finsupp.sum_single_index] at hd
  omega

/-- The first variable becomes the outer variable; the second becomes the inner one. -/
noncomputable def bivariateEquiv (R : Type*) [CommSemiring R] :
    MvPolynomial (Fin 2) R ≃ₐ[R] R[X][X] :=
  (MvPolynomial.finSuccEquiv R 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1)))

lemma bivariateEquiv_C (c : R) :
    bivariateEquiv R (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
  exact (bivariateEquiv R).commutes c

lemma bivariateEquiv_X_zero :
    bivariateEquiv R (MvPolynomial.X 0) = Polynomial.X := by
  simp only [bivariateEquiv, AlgEquiv.trans_apply, MvPolynomial.finSuccEquiv_X_zero,
    Polynomial.coe_mapAlgEquiv, Polynomial.map_X]

lemma bivariateEquiv_X_one :
    bivariateEquiv R (MvPolynomial.X 1) = Polynomial.C Polynomial.X := by
  rw [bivariateEquiv, AlgEquiv.trans_apply,
    show (1 : Fin 2) = (0 : Fin 1).succ from rfl, MvPolynomial.finSuccEquiv_X_succ]
  simp [Polynomial.coe_mapAlgEquiv, MvPolynomial.uniqueAlgEquiv_apply]

lemma bivariateEquiv_coeff (P : MvPolynomial (Fin 2) R) (j : ℕ) :
    (bivariateEquiv R P).coeff j =
      MvPolynomial.uniqueAlgEquiv R (Fin 1) ((MvPolynomial.finSuccEquiv R 1 P).coeff j) := by
  simp only [bivariateEquiv, AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv,
    Polynomial.coeff_map]
  rfl

lemma bivariateEquiv_coeff_degree (P : MvPolynomial (Fin 2) R) (j : ℕ)
    (hj : (bivariateEquiv R P).coeff j ≠ 0) :
    ((bivariateEquiv R P).coeff j).natDegree + j ≤ P.totalDegree := by
  have hcoeff : (MvPolynomial.finSuccEquiv R 1 P).coeff j ≠ 0 := by
    intro h
    rw [bivariateEquiv_coeff, h, map_zero] at hj
    exact hj rfl
  rw [bivariateEquiv_coeff]
  exact (Nat.add_le_add_right (natDegree_uniqueAlgEquiv_le _) j).trans
    (MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P j hcoeff)

lemma bivariateEquiv_eval {K : Type*} [CommRing K] (P : MvPolynomial (Fin 2) K) (x y : K) :
    bivariateEval x y (bivariateEquiv K P) = MvPolynomial.eval ![y, x] P := by
  have hhom : (bivariateEval x y).comp (bivariateEquiv K).toRingEquiv.toRingHom =
      MvPolynomial.eval ![y, x] := by
    ext i : 2
    · simp [RingHom.comp_apply, bivariateEquiv_C, bivariateEval]
    · fin_cases i
      · simp [RingHom.comp_apply, bivariateEquiv_X_zero, bivariateEval]
      · simp [RingHom.comp_apply, bivariateEquiv_X_one, bivariateEval]
  exact congrArg (fun φ : MvPolynomial (Fin 2) K →+* K => φ P) hhom

#print axioms bivariateEquiv_coeff_degree
-- 'Erdos477.Geometry.bivariateEquiv_coeff_degree' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
