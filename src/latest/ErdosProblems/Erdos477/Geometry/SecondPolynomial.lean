/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Embedding a univariate polynomial in the second plane coordinate.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.BivariateEquiv
import ErdosProblems.Erdos477.Geometry.QuadraticSixthReduction

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

noncomputable def secondPolynomial : K[X] →+* MvPolynomial (Fin 2) K :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X 1)

@[simp] lemma secondPolynomial_C (a : K) :
    secondPolynomial (C a) = MvPolynomial.C a := by
  simp [secondPolynomial]

@[simp] lemma secondPolynomial_X :
    secondPolynomial (X : K[X]) = MvPolynomial.X 1 := by
  simp [secondPolynomial]

lemma eval_secondPolynomial (p : K[X]) (z : Fin 2 → K) :
    MvPolynomial.eval z (secondPolynomial p) = p.eval (z 1) := by
  have h : (MvPolynomial.eval z).comp secondPolynomial = evalRingHom (z 1) := by
    ext a <;> simp
  exact congrArg (fun f : K[X] →+* K => f p) h

lemma bivariateEquiv_secondPolynomial (p : K[X]) :
    bivariateEquiv K (secondPolynomial p) = C p := by
  have h : (bivariateEquiv K).toRingEquiv.toRingHom.comp secondPolynomial = C := by
    ext a <;> simp [bivariateEquiv_C, bivariateEquiv_X_one]
  exact congrArg (fun f : K[X] →+* K[X][X] => f p) h

lemma secondPolynomial_injective : Function.Injective (secondPolynomial (K := K)) := by
  intro p q h
  apply C_injective
  simpa only [bivariateEquiv_secondPolynomial] using congrArg (bivariateEquiv K) h

lemma secondPolynomial_ne_zero {p : K[X]} (hp : p ≠ 0) : secondPolynomial p ≠ 0 :=
  fun h => hp (secondPolynomial_injective (h.trans (map_zero secondPolynomial).symm))

lemma totalDegree_secondPolynomial (p : K[X]) :
    (secondPolynomial p).totalDegree ≤ p.natDegree := by
  classical
  change (p.eval₂ MvPolynomial.C (MvPolynomial.X 1)).totalDegree ≤ _
  rw [eval₂_eq_sum, Polynomial.sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro n hn
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow, zero_add] using
    le_natDegree_of_mem_supp n hn

lemma secondPolynomial_quadraticSixthLinear (b c : K[X]) :
    secondPolynomial (quadraticSixthLinear b c) =
      quadraticSixthLinear (secondPolynomial b) (secondPolynomial c) := by
  simp only [quadraticSixthLinear, map_neg, map_mul, map_sub, map_pow, map_ofNat]

lemma secondPolynomial_quadraticSixthConstant (b c : K[X]) :
    secondPolynomial (quadraticSixthConstant b c) =
      quadraticSixthConstant (secondPolynomial b) (secondPolynomial c) := by
  simp only [quadraticSixthConstant, map_neg, map_add, map_mul, map_sub, map_pow, map_ofNat]

#print axioms totalDegree_secondPolynomial
-- 'Erdos477.Geometry.totalDegree_secondPolynomial' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
