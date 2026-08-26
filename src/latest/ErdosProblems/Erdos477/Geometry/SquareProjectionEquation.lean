/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The quartic plane equation and rational certificate for two prescribed squares.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SecondPolynomial
import ErdosProblems.Erdos477.Geometry.QuarticProjection
import ErdosProblems.Erdos477.Geometry.RationalLiftCertificate

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

noncomputable def squareProjectionEquation (h g : K[X]) : MvPolynomial (Fin 2) K :=
  quarticProjection (secondPolynomial h) (secondPolynomial g) (MvPolynomial.X 0)

noncomputable def squareProjectionNumerator (h g : K[X]) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 2 + secondPolynomial h - secondPolynomial g

noncomputable def squareProjectionDenominator : MvPolynomial (Fin 2) K :=
  2 * MvPolynomial.X 0

lemma squareProjectionEquation_ne_zero (h g : K[X]) : squareProjectionEquation h g ≠ 0 := by
  have heq : bivariateEquiv K (squareProjectionEquation h g) =
      X ^ 4 + C (-2 * (h + g)) * X ^ 2 + C ((h - g) ^ 2) := by
    simp only [squareProjectionEquation, quarticProjection, map_add, map_sub, map_mul,
      map_pow, map_ofNat, map_neg, bivariateEquiv_secondPolynomial, bivariateEquiv_X_zero]
    ring
  intro hz
  have hc := congrArg (fun p : K[X][X] => p.coeff 4) heq
  rw [hz, map_zero] at hc
  simp only [coeff_zero, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C] at hc
  norm_num at hc

lemma totalDegree_squareProjectionEquation (h g : K[X])
    (hh : h.natDegree ≤ 2) (hg : g.natDegree ≤ 2) :
    (squareProjectionEquation h g).totalDegree ≤ 4 := by
  have hH := (totalDegree_secondPolynomial h).trans hh
  have hG := (totalDegree_secondPolynomial g).trans hg
  have hsum := (MvPolynomial.totalDegree_add (secondPolynomial h) (secondPolynomial g)).trans
    (max_le hH hG)
  have hsub := (MvPolynomial.totalDegree_sub (secondPolynomial h) (secondPolynomial g)).trans
    (max_le hH hG)
  have htwo : (2 * (secondPolynomial h + secondPolynomial g)).totalDegree ≤ 2 := by
    have hc : ((2 : MvPolynomial (Fin 2) K)).totalDegree = 0 := by
      simpa only [map_ofNat] using MvPolynomial.totalDegree_C (σ := Fin 2) (2 : K)
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [hc, zero_add]
    exact hsum
  unfold squareProjectionEquation quarticProjection
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le (by simp)
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_X_pow]
    omega
  · exact (MvPolynomial.totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 hsub)

lemma squareProjectionEquation_dvd_certificate (k : K) (h g : K[X])
    (hsextic : h ^ 3 + g ^ 3 - X ^ 6 = C k) :
    squareProjectionEquation h g ∣ sexticRationalCertificate 1 k
      (squareProjectionNumerator h g) squareProjectionDenominator := by
  have hs : secondPolynomial h ^ 3 + secondPolynomial g ^ 3 - MvPolynomial.X 1 ^ 6 =
      MvPolynomial.C k := by
    simpa only [map_add, map_sub, map_pow, secondPolynomial_X, secondPolynomial_C] using
      congrArg secondPolynomial hsextic
  simpa only [squareProjectionEquation, squareProjectionNumerator, squareProjectionDenominator,
    sexticRationalCertificate, map_one, one_mul] using
    quartic_rational_certificate (secondPolynomial h) (secondPolynomial g)
      (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.C k) hs

lemma eval_squareProjectionEquation (u y x : K) (h g : K[X])
    (hu : u ^ 2 = h.eval x) (hy : y ^ 2 = g.eval x) :
    MvPolynomial.eval ![y + u, x] (squareProjectionEquation h g) = 0 := by
  simp only [squareProjectionEquation, quarticProjection, map_add, map_sub, map_mul,
    map_pow, map_ofNat, eval_secondPolynomial, MvPolynomial.eval_X,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  simpa only [quarticProjection, add_comm u y] using
    quarticProjection_of_squares u y (h.eval x) (g.eval x) hu hy

lemma eval_squareProjection_inverse (u y x : K) (h g : K[X])
    (hu : u ^ 2 = h.eval x) (hy : y ^ 2 = g.eval x) :
    MvPolynomial.eval ![y + u, x] (squareProjectionNumerator h g) =
      u * MvPolynomial.eval ![y + u, x] squareProjectionDenominator := by
  simp only [squareProjectionNumerator, squareProjectionDenominator, map_add, map_sub,
    map_mul, map_pow, map_ofNat, eval_secondPolynomial, MvPolynomial.eval_X,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [← hu, ← hy]
  ring

#print axioms squareProjectionEquation_dvd_certificate
-- 'Erdos477.Geometry.squareProjectionEquation_dvd_certificate' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
