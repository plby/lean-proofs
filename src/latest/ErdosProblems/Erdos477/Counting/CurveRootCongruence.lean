/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniqueness in a smooth curve chart modulo powers of a parameter.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CurveCoordinates

namespace Erdos477.Counting

open Polynomial
open Erdos477.Geometry

variable {R : Type*} [CommRing R]

theorem pow_dvd_curve_root_sub (P : R[X][X]) (q x y a b : R) (r : ℕ)
    (hcop : IsCoprime q ((P.map (evalRingHom a)).derivative.eval b))
    (hroot : (P.map (evalRingHom x)).eval y = 0)
    (hcenter : (P.map (evalRingHom a)).eval b = 0)
    (hx : q ∣ x - a) (hy : q ∣ y - b) (hfree : q ^ r ∣ x - a) : q ^ r ∣ y - b := by
  obtain ⟨v, w, hvw⟩ := hcop.symm
  have hv : q ∣ v * (P.map (evalRingHom a)).derivative.eval b - 1 := by
    refine ⟨-w, ?_⟩
    linear_combination hvw
  have hder : q ∣ v * (P.map (evalRingHom x)).derivative.eval y - 1 := by
    have hdiff := dvd_bivariate_eval_sub P.derivative q x y a b hx hy
    simp only [← Polynomial.derivative_map] at hdiff
    convert dvd_add (dvd_mul_of_dvd_right hdiff v) hv using 1
    ring
  let G := newtonApproximation P (C v) (C b) r
  have hGcenter : G.eval a = b := by
    rw [eval_newton_graph]
    exact newtonApproximation_eq_of_root _ v b hcenter r
  have herror : q ^ r ∣ y - G.eval x := (pow_dvd_pow q (Nat.le_succ r)).trans
    (pow_dvd_newton_graph_error P q v b x y r hroot hder hy)
  have hGdiff : q ^ r ∣ G.eval x - b := by
    rw [← hGcenter]
    exact hfree.trans (Polynomial.sub_dvd_eval_sub x a G)
  simpa only [sub_add_sub_cancel] using dvd_add herror hGdiff

theorem pow_dvd_curve_coordinate_sub (P : MvPolynomial (Fin 2) R) (q : R)
    (z a : Fin 2 → R) (r : ℕ)
    (hcop : IsCoprime q (MvPolynomial.eval a (MvPolynomial.pderiv 0 P)))
    (hroot : MvPolynomial.eval z P = 0) (hcenter : MvPolynomial.eval a P = 0)
    (hclass : ∀ k, q ∣ z k - a k) (hfree : q ^ r ∣ z 1 - a 1) : q ^ r ∣ z 0 - a 0 := by
  have ha : ![a 0, a 1] = a := by ext k; fin_cases k <;> rfl
  have hz : ![z 0, z 1] = z := by ext k; fin_cases k <;> rfl
  apply pow_dvd_curve_root_sub (bivariateEquiv R P) q (z 1) (z 0) (a 1) (a 0) r
  · simpa only [eval_derivative_bivariateEquiv_map, ha] using hcop
  · simpa only [eval_bivariateEquiv_map, hz] using hroot
  · simpa only [eval_bivariateEquiv_map, ha] using hcenter
  · exact hclass 1
  · exact hclass 0
  · exact hfree

#print axioms pow_dvd_curve_coordinate_sub
-- 'Erdos477.Counting.pow_dvd_curve_coordinate_sub' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
