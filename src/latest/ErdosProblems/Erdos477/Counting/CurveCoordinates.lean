/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Connecting the local curve determinant with two-variable polynomial coordinates.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.BivariateEquiv
import ErdosProblems.Erdos477.Counting.CurveLocalDeterminant

namespace Erdos477.Counting

open Polynomial
open Erdos477.Geometry

variable {R : Type*} [CommRing R]

lemma bivariateEquiv_pderiv_zero (P : MvPolynomial (Fin 2) R) :
    bivariateEquiv R (MvPolynomial.pderiv 0 P) = (bivariateEquiv R P).derivative := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [bivariateEquiv_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      fin_cases i
      · simp [hp, bivariateEquiv_X_zero, mul_comm]
      · simp [hp, bivariateEquiv_X_one, mul_comm]

lemma eval_bivariateEquiv_map (P : MvPolynomial (Fin 2) R) (x y : R) :
    ((bivariateEquiv R P).map (evalRingHom x)).eval y = MvPolynomial.eval ![y, x] P := by
  rw [eval_map]
  exact bivariateEquiv_eval P x y

lemma eval_derivative_bivariateEquiv_map (P : MvPolynomial (Fin 2) R) (x y : R) :
    ((bivariateEquiv R P).map (evalRingHom x)).derivative.eval y =
      MvPolynomial.eval ![y, x] (MvPolynomial.pderiv 0 P) := by
  rw [derivative_map, ← bivariateEquiv_pderiv_zero, eval_bivariateEquiv_map]

/-- The local determinant estimate expressed in the same coordinates as
the plane curve and its partial derivative. -/
theorem pow_dvd_curve_mv_eval_det_of_congruence {s : ℕ}
    (P : MvPolynomial (Fin 2) R) (F : Fin s → MvPolynomial (Fin 2) R)
    (q : R) (a : Fin 2 → R) (z : Fin s → Fin 2 → R)
    (hcop : IsCoprime q (MvPolynomial.eval a (MvPolynomial.pderiv 0 P)))
    (hroot : ∀ j, MvPolynomial.eval (z j) P = 0)
    (hclass : ∀ j k, q ∣ z j k - a k) :
    q ^ s.choose 2 ∣ Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) := by
  have ha : ![a 0, a 1] = a := by ext k; fin_cases k <;> rfl
  have hz (j) : ![z j 0, z j 1] = z j := by ext k; fin_cases k <;> rfl
  have h := pow_dvd_plane_curve_eval_det_of_congruence (bivariateEquiv R P)
    (fun i => bivariateEquiv R (F i)) q (a 1) (a 0) (fun j => z j 1) (fun j => z j 0)
    (by simpa only [eval_derivative_bivariateEquiv_map, ha] using hcop)
    (fun j => by simpa only [eval_bivariateEquiv_map, hz] using hroot j)
    (fun j => hclass j 1) (fun j => hclass j 0)
  simpa only [eval_bivariateEquiv_map, hz] using h

#print axioms pow_dvd_curve_mv_eval_det_of_congruence
-- 'Erdos477.Counting.pow_dvd_curve_mv_eval_det_of_congruence' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
