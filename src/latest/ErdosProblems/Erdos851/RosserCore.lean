/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# The finite Buchstab core of the Rosser sieve

This file isolates the exact combinatorial recursion behind upper and lower
Rosser weights.  It is independent of primes and of asymptotic estimates.
An ordered list is viewed as a descending list of possible sieve primes.
`buchstabChildren l` records every possible next selected prime together with
the smaller primes which may follow it.

At an upper node we may discard children which fail a stopping predicate; at
a lower node all children are retained.  The two evaluators alternate.  The
finite Buchstab identity then proves that the resulting lower evaluator is at
most the full Euler product and the upper evaluator is at least it.
-/

namespace Erdos851

open List

/-- Every possible next element of a list, paired with the suffix strictly
after it.  For `[p₁, p₂, p₃]` this is
`[(p₁,[p₂,p₃]), (p₂,[p₃]), (p₃,[])]`. -/
def buchstabChildren {α : Type*} : List α → List (α × List α)
  | [] => []
  | p :: ps => (p, ps) :: buchstabChildren ps

@[simp]
theorem buchstabChildren_nil {α : Type*} :
    buchstabChildren ([] : List α) = [] := rfl

@[simp]
theorem buchstabChildren_cons {α : Type*} (p : α) (ps : List α) :
    buchstabChildren (p :: ps) = (p, ps) :: buchstabChildren ps := rfl

/-- A child suffix is strictly shorter than its parent list. -/
theorem length_snd_lt_of_mem_buchstabChildren {α : Type*}
    {l : List α} {q : α × List α} (hq : q ∈ buchstabChildren l) :
    q.2.length < l.length := by
  induction l with
  | nil => simp at hq
  | cons p ps ih =>
      simp only [buchstabChildren_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · simp
      · exact (ih hq).trans (Nat.lt_succ_self _)

/-- The Euler product over an ordered finite list. -/
def buchstabProduct {α : Type*} (x : α → ℝ) (l : List α) : ℝ :=
  (l.map fun p => 1 - x p).prod

/-- Exact finite Buchstab identity for an Euler product. -/
theorem buchstabProduct_eq_one_sub_sum {α : Type*}
    (x : α → ℝ) (l : List α) :
    buchstabProduct x l =
      1 - ((buchstabChildren l).map fun q =>
        x q.1 * buchstabProduct x q.2).sum := by
  induction l with
  | nil => simp [buchstabProduct]
  | cons p ps ih =>
      simp only [buchstabProduct, List.map_cons, List.prod_cons,
        buchstabChildren_cons, List.sum_cons]
      change (1 - x p) * buchstabProduct x ps =
        1 - (x p * buchstabProduct x ps +
          ((buchstabChildren ps).map fun q =>
            x q.1 * buchstabProduct x q.2).sum)
      rw [ih]
      ring

/-- The Euler product is nonnegative when every local factor lies below one. -/
theorem buchstabProduct_nonneg {α : Type*} {x : α → ℝ}
    (hx1 : ∀ p, x p ≤ 1) (l : List α) :
    0 ≤ buchstabProduct x l := by
  unfold buchstabProduct
  apply List.prod_nonneg
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨p, _hp, rfl⟩ := hy
  exact sub_nonneg.mpr (hx1 p)

mutual

  /-- Upper Rosser--Buchstab evaluator with structural fuel.  The stopping
  predicate is tested only at upper nodes; its argument is the complete
  selected prefix, in descending order. -/
  def rosserUpperEval {α : Type*} (stop : List α → Bool) (x : α → ℝ) :
      ℕ → List α → List α → ℝ
    | 0, _selected, _remaining => 1
    | fuel + 1, selected, remaining =>
        1 - ((buchstabChildren remaining).map fun q =>
          if stop (selected ++ [q.1]) then
            x q.1 * rosserLowerEval stop x fuel (selected ++ [q.1]) q.2
          else 0).sum

  /-- Lower Rosser--Buchstab evaluator with structural fuel.  All children
  are retained at lower nodes. -/
  def rosserLowerEval {α : Type*} (stop : List α → Bool) (x : α → ℝ) :
      ℕ → List α → List α → ℝ
    | 0, _selected, _remaining => 1
    | fuel + 1, selected, remaining =>
        1 - ((buchstabChildren remaining).map fun q =>
          x q.1 * rosserUpperEval stop x fuel (selected ++ [q.1]) q.2).sum

end

/-- The exact finite Rosser inequality.  Once the fuel is at least the number
of remaining possible elements, the lower recursive evaluator lies below the
full Euler product and the upper recursive evaluator lies above it.

Taking every `x p` to be zero or one gives the pointwise lower/upper sieve
inequalities.  Taking `x p` to be a local density gives the corresponding
main-term inequalities. -/
theorem rosserLowerEval_le_product_le_upperEval {α : Type*}
    (stop : List α → Bool) (x : α → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p ≤ 1) :
    ∀ (fuel : ℕ) (selected remaining : List α),
      remaining.length ≤ fuel →
      rosserLowerEval stop x fuel selected remaining ≤
          buchstabProduct x remaining ∧
        buchstabProduct x remaining ≤
          rosserUpperEval stop x fuel selected remaining := by
  intro fuel
  induction fuel with
  | zero =>
      intro selected remaining hlen
      have hzero : remaining.length = 0 := Nat.eq_zero_of_le_zero hlen
      have hnil : remaining = [] := List.length_eq_zero_iff.mp hzero
      subst remaining
      simp [rosserLowerEval, rosserUpperEval, buchstabProduct]
  | succ fuel ih =>
      intro selected remaining hlen
      have htail : ∀ q ∈ buchstabChildren remaining, q.2.length ≤ fuel := by
        intro q hq
        exact Nat.lt_succ_iff.mp
          ((length_snd_lt_of_mem_buchstabChildren hq).trans_le hlen)
      constructor
      · rw [rosserLowerEval, buchstabProduct_eq_one_sub_sum]
        apply sub_le_sub_left
        apply List.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left
          (ih (selected ++ [q.1]) q.2 (htail q hq)).2 (hx0 q.1)
      · rw [rosserUpperEval, buchstabProduct_eq_one_sub_sum]
        apply sub_le_sub_left
        apply List.sum_le_sum
        intro q hq
        cases hstop : stop (selected ++ [q.1])
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact mul_nonneg (hx0 q.1) (buchstabProduct_nonneg hx1 q.2)
        · simp only [↓reduceIte]
          exact mul_le_mul_of_nonneg_left
            (ih (selected ++ [q.1]) q.2 (htail q hq)).1 (hx0 q.1)

end Erdos851
