import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Grouping finite sums by the cardinalities of label classes. -/

namespace Erdos556

open Finset

theorem sum_by_fiber_card {V P R : Type*} [Fintype V] [Fintype P] [DecidableEq P]
    [Semiring R] (label : V → P) (f : P → R) :
    (∑ v, f (label v)) = ∑ p, ((univ.filter (fun v => label v = p)).card : R) * f p := by
  classical
  have h := sum_fiberwise' (univ : Finset V) label f
  simpa only [sum_const, nsmul_eq_mul] using h.symm

theorem sum_fiber_card_eq {V P : Type*} [Fintype V] [Fintype P] [DecidableEq P]
    (label : V → P) : (∑ p, (univ.filter (fun v => label v = p)).card) = Fintype.card V := by
  simpa using (sum_by_fiber_card label (fun _ => (1 : ℕ))).symm

theorem sum_double_by_fiber_card {V P R : Type*} [Fintype V] [Fintype P] [DecidableEq P]
    [Semiring R] (label : V → P) (f : P → P → R) :
    (∑ u, ∑ v, f (label u) (label v)) =
      ∑ p, ∑ q, ((univ.filter (fun v => label v = p)).card : R) *
        ((univ.filter (fun v => label v = q)).card : R) * f p q := by
  classical
  calc
    _ = ∑ u, ∑ q, ((univ.filter (fun v => label v = q)).card : R) * f (label u) q := by
      apply sum_congr rfl
      intro u _
      exact sum_by_fiber_card label (f (label u))
    _ = ∑ p, ((univ.filter (fun v => label v = p)).card : R) *
        (∑ q, ((univ.filter (fun v => label v = q)).card : R) * f p q) :=
      sum_by_fiber_card label (fun p => ∑ q, ((univ.filter (fun v => label v = q)).card : R) * f p q)
    _ = _ := by simp only [mul_sum, mul_assoc]

end Erdos556
