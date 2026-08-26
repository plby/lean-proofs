/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The cleared sextic equation for a rational graph in the second coordinate.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SecondPolynomial
import ErdosProblems.Erdos477.Geometry.RationalLiftCertificate

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

noncomputable def rationalGraphEquation (k : K) (n d : K[X]) :
    MvPolynomial (Fin 2) K :=
  sexticRationalCertificate 0 k (secondPolynomial n) (secondPolynomial d)

lemma rationalGraphEquation_ne_zero (k : K) (n d : K[X]) (hd : d ≠ 0) :
    rationalGraphEquation k n d ≠ 0 := by
  have heq : bivariateEquiv K (rationalGraphEquation k n d) =
      C (d ^ 6) * X ^ 6 + C (n ^ 6 - X ^ 6 * d ^ 6 - C k * d ^ 6) := by
    simp only [rationalGraphEquation, sexticRationalCertificate, map_add, map_sub,
      map_mul, map_pow, map_zero, zero_mul, sub_zero, bivariateEquiv_secondPolynomial,
      bivariateEquiv_X_zero, bivariateEquiv_X_one, bivariateEquiv_C]
    ring
  intro h
  have hc := congrArg (fun p : K[X][X] => p.coeff 6) heq
  rw [h, map_zero] at hc
  simp only [coeff_zero, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C] at hc
  have hpow : d ^ 6 = 0 := by simpa using hc.symm
  exact pow_ne_zero 6 hd hpow

lemma totalDegree_rationalGraphEquation (k : K) (n d : K[X])
    (hn : n.natDegree ≤ 2) (hd : d.natDegree ≤ 1) :
    (rationalGraphEquation k n d).totalDegree ≤ 12 := by
  have hN := (totalDegree_secondPolynomial n).trans hn
  have hD := (totalDegree_secondPolynomial d).trans hd
  have hN6 := (MvPolynomial.totalDegree_pow (secondPolynomial n) 6).trans
    (Nat.mul_le_mul_left 6 hN)
  have hD6 := (MvPolynomial.totalDegree_pow (secondPolynomial d) 6).trans
    (Nat.mul_le_mul_left 6 hD)
  have hTD : (MvPolynomial.X 0 * secondPolynomial d).totalDegree ≤ 2 := by
    simpa only [MvPolynomial.totalDegree_X] using
      (MvPolynomial.totalDegree_mul (MvPolynomial.X 0) (secondPolynomial d)).trans
        (Nat.add_le_add le_rfl hD)
  unfold rationalGraphEquation sexticRationalCertificate
  simp only [map_zero, zero_mul, sub_zero]
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · apply (MvPolynomial.totalDegree_add _ _).trans
      exact max_le hN6 ((MvPolynomial.totalDegree_pow _ 6).trans (Nat.mul_le_mul_left 6 hTD))
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      rw [MvPolynomial.totalDegree_X_pow]
      omega
  · exact ((MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (MvPolynomial.totalDegree_C k).le hD6)).trans (by decide)

lemma eval_rationalGraphEquation (k t x y : K) (n d : K[X])
    (hinverse : n.eval x = y * d.eval x) (hsextic : t ^ 6 + y ^ 6 - x ^ 6 = k) :
    MvPolynomial.eval ![t, x] (rationalGraphEquation k n d) = 0 := by
  simp only [rationalGraphEquation, sexticRationalCertificate, map_zero, zero_mul, sub_zero,
    map_add, map_mul, map_pow, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
    eval_secondPolynomial, Matrix.cons_val_one, Matrix.cons_val_zero, hinverse]
  linear_combination (d.eval x) ^ 6 * hsextic

#print axioms rationalGraphEquation_ne_zero
-- 'Erdos477.Geometry.rationalGraphEquation_ne_zero' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
