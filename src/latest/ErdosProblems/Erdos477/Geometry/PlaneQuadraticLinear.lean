/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Plane quadratics whose squared first-coordinate coefficient vanishes.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.PlaneQuadratic
import ErdosProblems.Erdos477.Geometry.SecondPolynomial

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

noncomputable def planeLinearCoefficient (a : Fin 6 → K) : K[X] := C (a 1) * X + C (a 3)

noncomputable def planeConstantCoefficient (a : Fin 6 → K) : K[X] :=
  C (a 2) * X ^ 2 + C (a 4) * X + C (a 5)

lemma degree_planeLinearCoefficient (a : Fin 6 → K) :
    (planeLinearCoefficient a).natDegree ≤ 1 := natDegree_linear_le

lemma degree_planeConstantCoefficient (a : Fin 6 → K) :
    (planeConstantCoefficient a).natDegree ≤ 2 := by
  unfold planeConstantCoefficient
  rw [natDegree_add_C]
  apply (natDegree_add_le _ _).trans
  exact max_le ((natDegree_C_mul_le _ _).trans (by simp))
    ((natDegree_C_mul_le _ _).trans (by simp))

lemma planeQuadratic_eq_linear (a : Fin 6 → K) (ha : a 0 = 0) :
    planeQuadratic a = secondPolynomial (planeLinearCoefficient a) * MvPolynomial.X 0 +
      secondPolynomial (planeConstantCoefficient a) := by
  rw [planeQuadratic_eq]
  simp only [ha, map_zero, zero_mul, zero_add, planeLinearCoefficient, planeConstantCoefficient,
    map_add, map_mul, map_pow, secondPolynomial_C, secondPolynomial_X]
  ring

lemma bivariateEquiv_planeQuadratic_linear (a : Fin 6 → K) (ha : a 0 = 0) :
    bivariateEquiv K (planeQuadratic a) =
      C (planeLinearCoefficient a) * X + C (planeConstantCoefficient a) := by
  simp only [planeQuadratic_eq_linear a ha, map_add, map_mul,
    bivariateEquiv_secondPolynomial, bivariateEquiv_X_zero]

lemma eval_planeQuadratic_linear (a : Fin 6 → K) (ha : a 0 = 0) (y x : K) :
    MvPolynomial.eval ![y, x] (planeQuadratic a) =
      (planeLinearCoefficient a).eval x * y + (planeConstantCoefficient a).eval x := by
  simp only [planeQuadratic_eq_linear a ha, map_add, map_mul, eval_secondPolynomial,
    MvPolynomial.eval_X, Matrix.cons_val_one, Matrix.cons_val_zero]

lemma planeConstantCoefficient_ne_zero (a : Fin 6 → K) (ha : a 0 = 0)
    (hlinear : planeLinearCoefficient a = 0) (hP : planeQuadratic a ≠ 0) :
    planeConstantCoefficient a ≠ 0 := by
  intro hconstant
  rw [planeQuadratic_eq_linear a ha, hlinear, hconstant, map_zero, zero_mul, zero_add] at hP
  exact hP rfl

#print axioms planeQuadratic_eq_linear
-- 'Erdos477.Geometry.planeQuadratic_eq_linear' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
