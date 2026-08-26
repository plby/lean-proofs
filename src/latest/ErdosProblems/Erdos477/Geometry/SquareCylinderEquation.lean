/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Square cylinders and the linear-divisor certificates in the zero-trace case.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.RationalGraphEquation

namespace Erdos477.Geometry

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

lemma linear_sixth_divisor_identity (n d H : R) (hd : d ≠ 0)
    (hdiv : C d * X - C n ∣ X ^ 6 - C H) : n ^ 6 = H * d ^ 6 := by
  have hpow := sub_dvd_pow_sub_pow (C d * X) (C n : R[X]) 6
  have hmul := dvd_mul_of_dvd_right hdiv (C (d ^ 6))
  have hsub := dvd_sub hmul hpow
  have hid : C (d ^ 6) * (X ^ 6 - C H) - ((C d * X) ^ 6 - C n ^ 6) =
      C (n ^ 6 - H * d ^ 6) := by simp only [map_sub, map_mul, map_pow]; ring
  rw [hid] at hsub
  have hdegree : (C d * X - C n : R[X]).natDegree = 1 := by
    rw [sub_eq_add_neg, ← map_neg]
    exact natDegree_linear hd
  have hz := eq_zero_of_dvd_of_natDegree_lt hsub (by rw [hdegree, natDegree_C]; decide)
  exact sub_eq_zero.mp (C_eq_zero.mp hz)

variable {K : Type*} [Field K]

noncomputable def squareCylinderEquation (g : K[X]) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 2 - secondPolynomial g

noncomputable def zeroTraceEquation (k : K) (g : K[X]) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 6 - secondPolynomial (X ^ 6 + C k - g ^ 3)

lemma bivariateEquiv_squareCylinderEquation (g : K[X]) :
    bivariateEquiv K (squareCylinderEquation g) = X ^ 2 - C g := by
  simp only [squareCylinderEquation, map_sub, map_pow, bivariateEquiv_X_zero,
    bivariateEquiv_secondPolynomial]

lemma squareCylinderEquation_ne_zero (g : K[X]) : squareCylinderEquation g ≠ 0 := by
  intro hz
  have h := congrArg (bivariateEquiv K) hz
  rw [bivariateEquiv_squareCylinderEquation, map_zero] at h
  exact X_pow_sub_C_ne_zero (by decide : 0 < 2) g h

lemma totalDegree_squareCylinderEquation (g : K[X]) (hg : g.natDegree ≤ 2) :
    (squareCylinderEquation g).totalDegree ≤ 2 := by
  exact (MvPolynomial.totalDegree_sub _ _).trans
    (max_le (by simp) ((totalDegree_secondPolynomial g).trans hg))

lemma bivariateEquiv_zeroTraceEquation (k : K) (g : K[X]) :
    bivariateEquiv K (zeroTraceEquation k g) = X ^ 6 - C (X ^ 6 + C k - g ^ 3) := by
  simp only [zeroTraceEquation, map_sub, map_pow, bivariateEquiv_X_zero,
    bivariateEquiv_secondPolynomial]

lemma zeroTraceEquation_ne_zero (k : K) (g : K[X]) : zeroTraceEquation k g ≠ 0 := by
  intro hz
  have h := congrArg (bivariateEquiv K) hz
  rw [bivariateEquiv_zeroTraceEquation, map_zero] at h
  exact X_pow_sub_C_ne_zero (by decide : 0 < 6) _ h

lemma totalDegree_zeroTraceEquation (k : K) (g : K[X]) (hg : g.natDegree ≤ 2) :
    (zeroTraceEquation k g).totalDegree ≤ 6 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le (by simp)
  apply (totalDegree_secondPolynomial _).trans
  apply (natDegree_sub_le _ _).trans
  exact max_le (by simp) (natDegree_pow_le_of_le 3 hg)

lemma eval_zeroTraceEquation (k u y x : K) (g : K[X])
    (hy : y ^ 2 = g.eval x) (heq : u ^ 6 + y ^ 6 - x ^ 6 = k) :
    MvPolynomial.eval ![u, x] (zeroTraceEquation k g) = 0 := by
  simp only [zeroTraceEquation, map_sub, map_pow, MvPolynomial.eval_X,
    eval_secondPolynomial, eval_add, eval_pow, eval_X, eval_C,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [← hy]
  linear_combination heq

lemma squareCylinderEquation_dvd_rationalGraphEquation (k : K) (g n d : K[X])
    (hd : d ≠ 0) (hdiv : C d * X - C n ∣ X ^ 6 - C (X ^ 6 + C k - g ^ 3)) :
    squareCylinderEquation g ∣ rationalGraphEquation k n d := by
  have hid := linear_sixth_divisor_identity n d (X ^ 6 + C k - g ^ 3) hd hdiv
  have heq : secondPolynomial n ^ 6 =
      (MvPolynomial.X 1 ^ 6 + MvPolynomial.C k - secondPolynomial g ^ 3) *
        secondPolynomial d ^ 6 := by
    simpa only [map_pow, map_mul, map_add, map_sub, secondPolynomial_X, secondPolynomial_C] using
      congrArg secondPolynomial hid
  refine ⟨(MvPolynomial.X 0 ^ 4 + MvPolynomial.X 0 ^ 2 * secondPolynomial g +
    secondPolynomial g ^ 2) * secondPolynomial d ^ 6, ?_⟩
  dsimp only [rationalGraphEquation, sexticRationalCertificate, squareCylinderEquation]
  rw [map_zero, zero_mul, sub_zero]
  linear_combination heq

#print axioms squareCylinderEquation_dvd_rationalGraphEquation
-- 'Erdos477.Geometry.squareCylinderEquation_dvd_rationalGraphEquation' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
