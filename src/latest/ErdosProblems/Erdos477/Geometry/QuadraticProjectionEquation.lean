/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The degree-twelve projection equation when the quadratic sixth-power trace is nonzero.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SecondPolynomial
import ErdosProblems.Erdos477.Geometry.QuadraticSixthDegree
import ErdosProblems.Erdos477.Geometry.RationalLiftCertificate

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

noncomputable def quadraticProjectionNumerator (k : K) (b c : K[X]) :
    MvPolynomial (Fin 2) K :=
  secondPolynomial (X ^ 6 + C k - quadraticSixthConstant b c) - MvPolynomial.X 0 ^ 6

noncomputable def quadraticProjectionDenominator (b c : K[X]) :
    MvPolynomial (Fin 2) K := secondPolynomial (quadraticSixthLinear b c)

noncomputable def quadraticProjectionEquation (k : K) (b c : K[X]) :
    MvPolynomial (Fin 2) K :=
  let N := quadraticProjectionNumerator k b c
  let D := quadraticProjectionDenominator b c
  N ^ 2 + secondPolynomial b * N * D + secondPolynomial c * D ^ 2

lemma quadraticProjectionEquation_ne_zero (k : K) (b c : K[X]) :
    quadraticProjectionEquation k b c ≠ 0 := by
  let H := X ^ 6 + C k - quadraticSixthConstant b c
  let A := quadraticSixthLinear b c
  have heq : bivariateEquiv K (quadraticProjectionEquation k b c) =
      X ^ 12 + C (-2 * H - b * A) * X ^ 6 + C (H ^ 2 + b * H * A + c * A ^ 2) := by
    simp only [quadraticProjectionEquation, quadraticProjectionNumerator,
      quadraticProjectionDenominator, map_add, map_mul, map_pow, map_sub,
      bivariateEquiv_secondPolynomial, bivariateEquiv_X_zero]
    dsimp only [H, A]
    simp only [map_add, map_neg, map_sub, map_pow, map_ofNat]
    ring
  intro h
  have hc := congrArg (fun p : K[X][X] => p.coeff 12) heq
  rw [h, map_zero] at hc
  simp only [coeff_zero, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C] at hc
  norm_num at hc

lemma totalDegree_quadraticProjectionNumerator (k : K) (b c : K[X])
    (hb : b.natDegree ≤ 1) (hc : c.natDegree ≤ 2) :
    (quadraticProjectionNumerator k b c).totalDegree ≤ 6 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le _ (by simp)
  apply (totalDegree_secondPolynomial _).trans
  apply (natDegree_sub_le _ _).trans
  exact max_le (by simp) (degree_quadraticSixthConstant b c hb hc)

lemma totalDegree_quadraticProjectionDenominator (b c : K[X])
    (hb : b.natDegree ≤ 1) (hc : c.natDegree ≤ 2) :
    (quadraticProjectionDenominator b c).totalDegree ≤ 5 :=
  (totalDegree_secondPolynomial _).trans (degree_quadraticSixthLinear b c hb hc)

lemma totalDegree_quadraticProjectionEquation (k : K) (b c : K[X])
    (hb : b.natDegree ≤ 1) (hc : c.natDegree ≤ 2) :
    (quadraticProjectionEquation k b c).totalDegree ≤ 12 := by
  have hN := totalDegree_quadraticProjectionNumerator k b c hb hc
  have hD := totalDegree_quadraticProjectionDenominator b c hb hc
  have hB := (totalDegree_secondPolynomial b).trans hb
  have hC := (totalDegree_secondPolynomial c).trans hc
  have hN2 := (MvPolynomial.totalDegree_pow (quadraticProjectionNumerator k b c) 2).trans
    (Nat.mul_le_mul_left 2 hN)
  have hD2 := (MvPolynomial.totalDegree_pow (quadraticProjectionDenominator b c) 2).trans
    (Nat.mul_le_mul_left 2 hD)
  unfold quadraticProjectionEquation
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_add _ _).trans
    exact max_le hN2 ((MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add ((MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hB hN)) hD))
  · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hC hD2)

lemma quadraticProjectionEquation_dvd_certificate (k : K) (b c : K[X]) :
    quadraticProjectionEquation k b c ∣ sexticRationalCertificate 0 k
      (quadraticProjectionNumerator k b c) (quadraticProjectionDenominator b c) := by
  refine ⟨quadraticSixthHomogeneousQuotient (secondPolynomial b) (secondPolynomial c)
    (quadraticProjectionNumerator k b c) (quadraticProjectionDenominator b c), ?_⟩
  have h := quadratic_remainder_certificate (secondPolynomial b) (secondPolynomial c)
    (quadraticProjectionNumerator k b c) (quadraticProjectionDenominator b c)
    (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.C k)
    (secondPolynomial_quadraticSixthLinear b c) (by
      simp only [quadraticProjectionNumerator, map_sub, map_add, map_pow,
        secondPolynomial_X, secondPolynomial_C, secondPolynomial_quadraticSixthConstant]
      ring)
  simpa only [sexticRationalCertificate, map_zero, zero_mul, sub_zero,
    quadraticProjectionEquation] using h

lemma eval_quadraticProjection_inverse (k t x y : K) (b c : K[X])
    (hquad : y ^ 2 + b.eval x * y + c.eval x = 0)
    (hsextic : t ^ 6 + y ^ 6 - x ^ 6 = k) :
    MvPolynomial.eval ![t, x] (quadraticProjectionNumerator k b c) =
      y * MvPolynomial.eval ![t, x] (quadraticProjectionDenominator b c) := by
  have h := sixth_eq_quadratic_remainder (b.eval x) (c.eval x) y hquad
  simp only [quadraticProjectionNumerator, quadraticProjectionDenominator, map_sub,
    eval_secondPolynomial, Matrix.cons_val_one, Matrix.cons_val_zero, map_pow,
    MvPolynomial.eval_X, eval_add, eval_pow, eval_X, eval_C]
  have hA : (quadraticSixthLinear b c).eval x = quadraticSixthLinear (b.eval x) (c.eval x) := by
    simp only [quadraticSixthLinear, eval_mul, eval_neg, eval_sub, eval_pow, eval_ofNat]
  have hD : (quadraticSixthConstant b c).eval x =
      quadraticSixthConstant (b.eval x) (c.eval x) := by
    simp only [quadraticSixthConstant, eval_mul, eval_add, eval_neg, eval_sub, eval_pow,
      eval_ofNat]
  rw [hA, hD]
  linear_combination h - hsextic

lemma eval_quadraticProjectionEquation (k t x y : K) (b c : K[X])
    (hquad : y ^ 2 + b.eval x * y + c.eval x = 0)
    (hsextic : t ^ 6 + y ^ 6 - x ^ 6 = k) :
    MvPolynomial.eval ![t, x] (quadraticProjectionEquation k b c) = 0 := by
  have hN := eval_quadraticProjection_inverse k t x y b c hquad hsextic
  simp only [quadraticProjectionEquation, map_add, map_mul, map_pow,
    eval_secondPolynomial, Matrix.cons_val_one, Matrix.cons_val_zero, hN]
  linear_combination
    (MvPolynomial.eval ![t, x] (quadraticProjectionDenominator b c)) ^ 2 * hquad

#print axioms quadraticProjectionEquation_dvd_certificate
-- 'Erdos477.Geometry.quadraticProjectionEquation_dvd_certificate' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
