/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Bounding the points where the chosen plane-curve derivative vanishes.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CurveCoordinates
import ErdosProblems.Erdos477.Geometry.IntegerPlaneBezout

namespace Erdos477.Geometry

open Polynomial

variable {σ R : Type*} [CommSemiring R]

lemma totalDegree_pderiv_le (P : MvPolynomial σ R) (i : σ) :
    (MvPolynomial.pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
  classical
  apply Finset.sup_le
  intro m hm
  have hcoeff := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hcoeff
  have hmP : m + Finsupp.single i 1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hcoeff)
  have hdeg := MvPolynomial.le_totalDegree hmP
  rw [Finsupp.sum_add_index (by simp) (by intros; simp), Finsupp.sum_single_index (by simp)] at hdeg
  omega

lemma bivariateEquiv_natDegree (P : MvPolynomial (Fin 2) R) :
    (bivariateEquiv R P).natDegree = P.degreeOf 0 := by
  rw [bivariateEquiv, AlgEquiv.trans_apply, Polynomial.coe_mapAlgEquiv,
    Polynomial.natDegree_map_eq_of_injective (MvPolynomial.uniqueAlgEquiv R (Fin 1)).injective,
    MvPolynomial.natDegree_finSuccEquiv]

variable {K : Type*} [Field K] [CharZero K]

lemma pderiv_zero_ne_zero (P : MvPolynomial (Fin 2) K) (hP : 0 < P.degreeOf 0) :
    MvPolynomial.pderiv 0 P ≠ 0 := by
  intro hzero
  have h := Counting.bivariateEquiv_pderiv_zero P
  rw [hzero, map_zero] at h
  have hdegree := Polynomial.derivative_eq_zero.mp h.symm
  rw [bivariateEquiv_natDegree] at hdegree
  omega

/-- At most `degree(P)*(degree(P)-1)` integer points on the curve have
vanishing first partial derivative. -/
theorem card_integer_curve_critical_points_le (P : MvPolynomial (Fin 2) ℤ)
    (hP : Irreducible (MvPolynomial.map (Int.castRingHom K) P))
    (hdegree : 0 < P.degreeOf 0) (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, MvPolynomial.eval z P = 0 ∧
      MvPolynomial.eval z (MvPolynomial.pderiv 0 P) = 0) :
    S.card ≤ P.totalDegree * (P.totalDegree - 1) := by
  have hQ0 : MvPolynomial.map (Int.castRingHom K) (MvPolynomial.pderiv 0 P) ≠ 0 := by
    rw [← MvPolynomial.pderiv_map]
    apply pderiv_zero_ne_zero
    rwa [degreeOf_map_of_injective _ Int.cast_injective]
  have hdiv : ¬ MvPolynomial.map (Int.castRingHom K) P ∣
      MvPolynomial.map (Int.castRingHom K) (MvPolynomial.pderiv 0 P) := by
    intro h
    have hdeg := MvPolynomial.totalDegree_le_of_dvd_of_isDomain h hQ0
    rw [totalDegree_map_of_injective _ Int.cast_injective,
      totalDegree_map_of_injective _ Int.cast_injective] at hdeg
    have hupper := totalDegree_pderiv_le P 0
    have hpos := (MvPolynomial.degreeOf_le_totalDegree P 0).trans_lt'
      hdegree
    omega
  exact (card_integer_plane_common_zeroes_le (K := K) P (MvPolynomial.pderiv 0 P)
    hP hdiv S hS).trans (Nat.mul_le_mul_left _ (totalDegree_pderiv_le P 0))

#print axioms card_integer_curve_critical_points_le
-- 'Erdos477.Geometry.card_integer_curve_critical_points_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
