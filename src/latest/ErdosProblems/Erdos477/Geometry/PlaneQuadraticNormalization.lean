/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Monic normalization of a plane quadratic with a nonzero squared first-variable coefficient.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.PlaneQuadratic
import ErdosProblems.Erdos477.Geometry.BivariateEquiv

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

noncomputable def normalizedQuadraticTrace (a : Fin 6 → K) : K[X] :=
  C ((a 0)⁻¹) * (C (a 1) * X + C (a 3))

noncomputable def normalizedQuadraticConstant (a : Fin 6 → K) : K[X] :=
  C ((a 0)⁻¹) * (C (a 2) * X ^ 2 + C (a 4) * X + C (a 5))

lemma degree_normalizedQuadraticTrace (a : Fin 6 → K) :
    (normalizedQuadraticTrace a).natDegree ≤ 1 := by
  exact (natDegree_C_mul_le _ _).trans natDegree_linear_le

lemma degree_normalizedQuadraticConstant (a : Fin 6 → K) :
    (normalizedQuadraticConstant a).natDegree ≤ 2 := by
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_add_C]
  apply (natDegree_add_le _ _).trans
  exact max_le ((natDegree_C_mul_le _ _).trans (by simp))
    ((natDegree_C_mul_le _ _).trans (by simp))

lemma bivariateEquiv_planeQuadratic_normalized (a : Fin 6 → K) (ha : a 0 ≠ 0) :
    bivariateEquiv K (planeQuadratic a) = C (C (a 0)) *
      (X ^ 2 + C (normalizedQuadraticTrace a) * X + C (normalizedQuadraticConstant a)) := by
  have hinv : C (C (a 0)) * C (C ((a 0)⁻¹)) = (1 : K[X][X]) := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
  rw [planeQuadratic_eq]
  simp only [map_add, map_mul, map_pow, bivariateEquiv_C,
    bivariateEquiv_X_zero, bivariateEquiv_X_one,
    normalizedQuadraticTrace, normalizedQuadraticConstant]
  linear_combination -(C (C (a 1)) * C X * X + C (C (a 3)) * X +
    C (C (a 2)) * C X ^ 2 + C (C (a 4)) * C X + C (C (a 5))) * hinv

lemma irreducible_normalized_planeQuadratic (a : Fin 6 → K) (ha : a 0 ≠ 0)
    (hP : Irreducible (planeQuadratic a)) :
    Irreducible (X ^ 2 + C (normalizedQuadraticTrace a) * X +
      C (normalizedQuadraticConstant a)) := by
  have h := (MulEquiv.irreducible_iff (bivariateEquiv K)).mpr hP
  rw [bivariateEquiv_planeQuadratic_normalized a ha] at h
  have hunit : IsUnit (C (C (a 0)) : K[X][X]) :=
    ((isUnit_iff_ne_zero.mpr ha).map Polynomial.C).map Polynomial.C
  exact (associated_unit_mul_right _ _ hunit).irreducible_iff.mpr h

lemma eval_planeQuadratic_normalized (a : Fin 6 → K) (ha : a 0 ≠ 0) (y x : K) :
    MvPolynomial.eval ![y, x] (planeQuadratic a) =
      a 0 * (y ^ 2 + (normalizedQuadraticTrace a).eval x * y +
        (normalizedQuadraticConstant a).eval x) := by
  have h := congrArg (bivariateEval x y) (bivariateEquiv_planeQuadratic_normalized a ha)
  rw [bivariateEquiv_eval] at h
  simpa [bivariateEval] using h

lemma planeQuadratic_root_iff_normalized (a : Fin 6 → K) (ha : a 0 ≠ 0) (y x : K) :
    MvPolynomial.eval ![y, x] (planeQuadratic a) = 0 ↔
      y ^ 2 + (normalizedQuadraticTrace a).eval x * y +
        (normalizedQuadraticConstant a).eval x = 0 := by
  rw [eval_planeQuadratic_normalized a ha, mul_eq_zero, or_iff_right ha]

#print axioms irreducible_normalized_planeQuadratic
-- 'Erdos477.Geometry.irreducible_normalized_planeQuadratic' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
