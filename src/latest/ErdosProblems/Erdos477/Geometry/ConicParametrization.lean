/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Explicit quadratic homogeneous coordinates for a nonsingular conic at the origin.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.PlaneQuadratic

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

noncomputable def conicNumerator (d e : K) : K[X] := -(C d + C e * X)

noncomputable def conicDenominator (a b c : K) : K[X] := C a + C b * X + C c * X ^ 2

noncomputable def conicCoordinates (a b c d e : K) : Fin 3 → K[X] :=
  ![conicNumerator d e, X * conicNumerator d e, conicDenominator a b c]

lemma degree_conicNumerator (d e : K) : (conicNumerator d e).natDegree ≤ 1 := by
  rw [conicNumerator, natDegree_neg]
  exact (natDegree_add_le _ _).trans
    (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))

lemma degree_conicDenominator (a b c : K) : (conicDenominator a b c).natDegree ≤ 2 := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    exact max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))
  · exact (natDegree_C_mul_le _ _).trans (by simp)

lemma degree_conicCoordinates (a b c d e : K) (i : Fin 3) :
    (conicCoordinates a b c d e i).natDegree ≤ 2 := by
  fin_cases i
  · exact (degree_conicNumerator d e).trans (by decide)
  · exact (natDegree_mul_le.trans (Nat.add_le_add (by simp) (degree_conicNumerator d e)))
  · exact degree_conicDenominator a b c

lemma conicCoordinates_identity (a b c d e : K) :
    C a * (conicCoordinates a b c d e 0) ^ 2 +
      C b * conicCoordinates a b c d e 0 * conicCoordinates a b c d e 1 +
      C c * (conicCoordinates a b c d e 1) ^ 2 +
      C d * conicCoordinates a b c d e 0 * conicCoordinates a b c d e 2 +
      C e * conicCoordinates a b c d e 1 * conicCoordinates a b c d e 2 = 0 := by
  change C a * conicNumerator d e ^ 2 + C b * conicNumerator d e * (X * conicNumerator d e) +
    C c * (X * conicNumerator d e) ^ 2 +
    C d * conicNumerator d e * conicDenominator a b c +
    C e * (X * conicNumerator d e) * conicDenominator a b c = 0
  dsimp only [conicNumerator, conicDenominator]
  ring

lemma conicCoordinates_no_common_root (a b c d e : K)
    (h : a * e ^ 2 - b * d * e + c * d ^ 2 ≠ 0) (r : K) :
    ¬ ∀ i, (conicCoordinates a b c d e i).eval r = 0 := by
  intro hr
  have h0 := hr 0
  have h2 := hr 2
  simp [conicCoordinates, conicNumerator, conicDenominator] at h0 h2
  apply h
  linear_combination e ^ 2 * h2 + (b * e + c * (e * r - d)) * h0

lemma conicCoordinates_degree_two (a b c d e : K) (he : e ≠ 0) :
    (conicCoordinates a b c d e 1).natDegree = 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (degree_conicCoordinates a b c d e 1)
  have hcoeff : (conicCoordinates a b c d e 1).coeff 2 = -e := by
    change (X * -(C d + C e * X) : K[X]).coeff 2 = -e
    have hexpand : (X * -(C d + C e * X) : K[X]) = -(C d * X) - C e * X ^ 2 := by ring
    rw [hexpand, coeff_sub, coeff_neg]
    norm_num [coeff_C_mul_X, coeff_C_mul_X_pow]
  rw [hcoeff]
  exact neg_ne_zero.mpr he

lemma conicCoordinates_at_base (a b c d e : K) (he : e ≠ 0)
    (h : a * e ^ 2 - b * d * e + c * d ^ 2 ≠ 0) :
    ∃ v : K, v ≠ 0 ∧
      (conicCoordinates a b c d e 0).eval (-d / e) = 0 ∧
      (conicCoordinates a b c d e 1).eval (-d / e) = 0 ∧
      (conicCoordinates a b c d e 2).eval (-d / e) = v := by
  have hnum : (conicNumerator d e).eval (-d / e) = 0 := by
    simp only [conicNumerator, eval_neg, eval_add, eval_C, eval_mul, eval_X]
    field_simp
    ring
  refine ⟨(conicDenominator a b c).eval (-d / e), ?_, hnum, ?_, rfl⟩
  · intro hden
    apply conicCoordinates_no_common_root a b c d e h (-d / e)
    intro i
    fin_cases i
    · exact hnum
    · change (X * conicNumerator d e).eval (-d / e) = 0
      rw [eval_mul, hnum, mul_zero]
    · exact hden
  · change (X * conicNumerator d e).eval (-d / e) = 0
    rw [eval_mul, hnum, mul_zero]

#print axioms conicCoordinates_at_base
-- 'Erdos477.Geometry.conicCoordinates_at_base' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
