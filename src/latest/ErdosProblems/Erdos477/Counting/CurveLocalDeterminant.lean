/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The local determinant estimate on a general plane curve, with its graph constructed.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.NewtonApproximation
import ErdosProblems.Erdos477.Counting.UnivariateDeterminant

namespace Erdos477.Counting

open Polynomial

variable {R : Type*} [CommRing R]

lemma bivariate_eval_commute (P : R[X][X]) (x y : R) :
    (P.map (evalRingHom x)).eval y = (P.eval (C y)).eval x := by
  simpa only [Polynomial.coe_evalRingHom, eval_C] using
    Polynomial.eval_map_apply (evalRingHom x) (C y) (p := P)

lemma dvd_bivariate_eval_sub (P : R[X][X]) (q x y a b : R)
    (hx : q ∣ x - a) (hy : q ∣ y - b) :
    q ∣ (P.map (evalRingHom x)).eval y - (P.map (evalRingHom a)).eval b := by
  have hfirst := hx.trans (Polynomial.sub_dvd_eval_sub x a (P.eval (C y)))
  rw [← bivariate_eval_commute, ← bivariate_eval_commute] at hfirst
  have hsecond := hy.trans (Polynomial.sub_dvd_eval_sub y b (P.map (evalRingHom a)))
  simpa only [sub_add_sub_cancel] using dvd_add hfirst hsecond

/-- The inner variable is free and the outer variable is solved by finite
Newton iteration. Evaluation commutes with every iteration. -/
lemma eval_newton_graph (P : R[X][X]) (v b x : R) (N : ℕ) :
    (newtonApproximation P (C v) (C b) N).eval x =
      newtonApproximation (P.map (evalRingHom x)) v b N := by
  simpa only [Polynomial.coe_evalRingHom, eval_C] using
    map_newtonApproximation (evalRingHom x) P (C v) (C b) N

lemma pow_dvd_newton_graph_error (P : R[X][X]) (q v b x y : R) (N : ℕ)
    (hroot : (P.map (evalRingHom x)).eval y = 0)
    (hder : q ∣ v * (P.map (evalRingHom x)).derivative.eval y - 1)
    (hbase : q ∣ y - b) :
    q ^ (N + 1) ∣ y - (newtonApproximation P (C v) (C b) N).eval x := by
  rw [eval_newton_graph]
  exact pow_dvd_newtonApproximation_error _ q y v b hroot hder hbase N

/-- Every polynomial restricted to the curve is congruent to a polynomial
in the free variable, to arbitrary finite order. -/
lemma pow_dvd_curve_polynomial_graph_error (P F : R[X][X]) (q v b x y : R) (N : ℕ)
    (hroot : (P.map (evalRingHom x)).eval y = 0)
    (hder : q ∣ v * (P.map (evalRingHom x)).derivative.eval y - 1)
    (hbase : q ∣ y - b) :
    q ^ (N + 1) ∣ (F.map (evalRingHom x)).eval y -
      (F.eval (newtonApproximation P (C v) (C b) N)).eval x := by
  have h := (pow_dvd_newton_graph_error P q v b x y N hroot hder hbase).trans
    (Polynomial.sub_dvd_eval_sub y ((newtonApproximation P (C v) (C b) N).eval x)
      (F.map (evalRingHom x)))
  have heq : (F.map (evalRingHom x)).eval
      ((newtonApproximation P (C v) (C b) N).eval x) =
      (F.eval (newtonApproximation P (C v) (C b) N)).eval x :=
    Polynomial.eval_map_apply (evalRingHom x) _
  rwa [heq] at h

/-- A common inverse derivative modulo `q` yields the optimal one-dimensional
local divisor for all evaluation determinants on the plane curve. -/
theorem pow_dvd_plane_curve_eval_det {s : ℕ} (P : R[X][X]) (F : Fin s → R[X][X])
    (q v a b : R) (x y : Fin s → R)
    (hroot : ∀ j, (P.map (evalRingHom (a + q * x j))).eval (y j) = 0)
    (hder : ∀ j, q ∣ v * (P.map (evalRingHom (a + q * x j))).derivative.eval (y j) - 1)
    (hbase : ∀ j, q ∣ y j - b) :
    q ^ s.choose 2 ∣ Matrix.det (Matrix.of fun i j =>
      ((F i).map (evalRingHom (a + q * x j))).eval (y j)) := by
  let N := s.choose 2
  let G : Fin s → R[X] := fun i => (F i).eval (newtonApproximation P (C v) (C b) N)
  apply pow_dvd_det_of_approximation q N (N + 1) (Nat.le_succ N) _
    (Matrix.of fun i j => (G i).eval (a + q * x j))
  · intro i j
    exact pow_dvd_curve_polynomial_graph_error P (F i) q v b (a + q * x j) (y j) N
      (hroot j) (hder j) (hbase j)
  · exact pow_dvd_univariate_eval_det_translate q a G x

/-- The usual smooth-residue-class hypothesis supplies the inverse derivative
and hence the determinant divisor. This works over the integers directly. -/
theorem pow_dvd_plane_curve_eval_det_of_congruence {s : ℕ}
    (P : R[X][X]) (F : Fin s → R[X][X]) (q a b : R) (x y : Fin s → R)
    (hcop : IsCoprime q ((P.map (evalRingHom a)).derivative.eval b))
    (hroot : ∀ j, (P.map (evalRingHom (x j))).eval (y j) = 0)
    (hx : ∀ j, q ∣ x j - a) (hy : ∀ j, q ∣ y j - b) :
    q ^ s.choose 2 ∣ Matrix.det (Matrix.of fun i j =>
      ((F i).map (evalRingHom (x j))).eval (y j)) := by
  obtain ⟨v, w, hvw⟩ := hcop.symm
  have hv : q ∣ v * (P.map (evalRingHom a)).derivative.eval b - 1 := by
    refine ⟨-w, ?_⟩
    linear_combination hvw
  choose z hz using hx
  have hcoord (j) : x j = a + q * z j := by linear_combination hz j
  have hder (j) : q ∣ v * (P.map (evalRingHom (x j))).derivative.eval (y j) - 1 := by
    have hdiff := dvd_bivariate_eval_sub P.derivative q (x j) (y j) a b ⟨z j, hz j⟩ (hy j)
    simp only [← Polynomial.derivative_map] at hdiff
    have h := dvd_add (dvd_mul_of_dvd_right hdiff v) hv
    convert h using 1
    ring
  have h := pow_dvd_plane_curve_eval_det P F q v a b z y
    (fun j => by rw [← hcoord]; exact hroot j)
    (fun j => by rw [← hcoord]; exact hder j) hy
  simpa only [← hcoord] using h

#print axioms pow_dvd_plane_curve_eval_det
-- 'Erdos477.Counting.pow_dvd_plane_curve_eval_det' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms pow_dvd_plane_curve_eval_det_of_congruence
-- 'Erdos477.Counting.pow_dvd_plane_curve_eval_det_of_congruence' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
