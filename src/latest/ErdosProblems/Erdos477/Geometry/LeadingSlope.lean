/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A bounded choice of direction that preserves the degree of a plane polynomial.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.Shear
import ErdosProblems.Erdos477.Geometry.CurveCriticalPoints

namespace Erdos477.Geometry

open scoped BigOperators
open Polynomial

variable {K : Type*} [Field K]

noncomputable def leadingSlope (P : MvPolynomial (Fin 2) K) : K[X] :=
  ∑ m ∈ P.support.filter (fun m => m 0 + m 1 = P.totalDegree),
    Polynomial.monomial (m 1) (P.coeff m * (-1) ^ m 1)

lemma natDegree_leadingSlope (P : MvPolynomial (Fin 2) K) :
    (leadingSlope P).natDegree ≤ P.totalDegree := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp only [leadingSlope, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro m hm
  have hdeg := (Finset.mem_filter.mp hm).2
  have hne : m 1 ≠ n := by omega
  simp only [Polynomial.coeff_monomial, if_neg hne]

lemma leadingSlope_ne_zero (P : MvPolynomial (Fin 2) K) (hP : P ≠ 0) :
    leadingSlope P ≠ 0 := by
  classical
  obtain ⟨m, hm, htop⟩ := Finset.exists_mem_eq_sup P.support
    (MvPolynomial.support_nonempty.mpr hP) (fun m => m.sum (fun _ e => e))
  have htop' : m 0 + m 1 = P.totalDegree := by
    change P.totalDegree = m.sum (fun _ e => e) at htop
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at htop
    exact htop.symm
  have hcoeff : (leadingSlope P).coeff (m 1) = P.coeff m * (-1) ^ m 1 := by
    simp only [leadingSlope, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single m]
    · simp
    · intro a ha hne
      have hatop := (Finset.mem_filter.mp ha).2
      have hne' : a 1 ≠ m 1 := by
        intro h
        apply hne
        ext i
        fin_cases i
        · change a 0 = m 0
          omega
        · exact h
      simp only [Polynomial.coeff_monomial, if_neg hne']
    · intro h
      exact (h (Finset.mem_filter.mpr ⟨hm, htop'⟩)).elim
  intro hzero
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp hm)
    (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))) hcoeff.symm

noncomputable def lineRestriction (a : K) : MvPolynomial (Fin 2) K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, Polynomial.C (-a) * Polynomial.X]

lemma lineRestriction_monomial (a c : K) (m : Fin 2 →₀ ℕ) :
    lineRestriction a (MvPolynomial.monomial m c) =
      Polynomial.C (c * (-a) ^ m 1) * Polynomial.X ^ (m 0 + m 1) := by
  rw [lineRestriction, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_pow, map_mul, map_pow, pow_add]
  ring

lemma coeff_lineRestriction_top (a : K) (P : MvPolynomial (Fin 2) K) :
    (lineRestriction a P).coeff P.totalDegree = (leadingSlope P).eval a := by
  classical
  have hsum : lineRestriction a P = ∑ m ∈ P.support,
      lineRestriction a (MvPolynomial.monomial m (P.coeff m)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
  rw [hsum]
  simp only [Polynomial.finsetSum_coeff, lineRestriction_monomial,
    Polynomial.coeff_C_mul_X_pow, leadingSlope, Polynomial.eval_finsetSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : m 0 + m 1 = P.totalDegree
  · simp only [h, if_true, Polynomial.eval_monomial]
    rw [neg_eq_neg_one_mul a, mul_pow]
    ring
  · simp only [h, Ne.symm h, if_false, Polynomial.eval_zero]

lemma lineRestriction_eq_map (a : K) (P : MvPolynomial (Fin 2) K) :
    lineRestriction a P = (bivariateEquiv K (shear a P)).map (Polynomial.evalRingHom 0) := by
  have hhom : lineRestriction a =
      ((Polynomial.mapRingHom (Polynomial.evalRingHom 0)).comp
        (bivariateEquiv K).toRingHom).comp (shear a) := by
    ext i : 2
    · simp [lineRestriction, bivariateEquiv_C]
    · fin_cases i
      · simp [lineRestriction, bivariateEquiv_X_zero]
      · simp [lineRestriction, bivariateEquiv_X_zero, bivariateEquiv_X_one,
          bivariateEquiv_C, neg_mul]
  exact congrArg (fun f : MvPolynomial (Fin 2) K →+* K[X] => f P) hhom

lemma degreeOf_shear_eq_of_leadingSlope_ne_zero (a : K) (P : MvPolynomial (Fin 2) K)
    (ha : (leadingSlope P).eval a ≠ 0) : (shear a P).degreeOf 0 = P.totalDegree := by
  apply le_antisymm
  · exact (MvPolynomial.degreeOf_le_totalDegree _ _).trans_eq (totalDegree_shear a P)
  · have hlow := Polynomial.le_natDegree_of_ne_zero
      (show (lineRestriction a P).coeff P.totalDegree ≠ 0 by rwa [coeff_lineRestriction_top])
    rw [lineRestriction_eq_map] at hlow
    exact hlow.trans (Polynomial.natDegree_map_le.trans_eq (bivariateEquiv_natDegree _))

#print axioms degreeOf_shear_eq_of_leadingSlope_ne_zero
-- 'Erdos477.Geometry.degreeOf_shear_eq_of_leadingSlope_ne_zero' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
