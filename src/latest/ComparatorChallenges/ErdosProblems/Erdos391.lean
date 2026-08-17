/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 391: decomposing a factorial into large factors.

The mathematical reconstruction and the correspondence between the published
argument and this development are documented in `tex/391.tex`.
-/

import Mathlib

open Filter Real
open scoped BigOperators Topology

namespace Erdos391

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A positive, nondecreasing `n`-tuple whose product is `n!`. -/
def IsFactorialRepresentation (n : ℕ) (a : Fin n → ℕ) : Prop :=
  (∀ i, 0 < a i) ∧ Monotone a ∧ ∏ i, a i = n.factorial

/-- The threshold `k` can be attained by a representation of `n!` with `n`
factors.  Requiring every factor to be at least `k` is equivalent to requiring
the first factor of the sorted representation to be at least `k`. -/
def Feasible (n k : ℕ) : Prop :=
  0 < k ∧ ∃ a : Fin n → ℕ, IsFactorialRepresentation n a ∧ ∀ i, k ≤ a i

/-- The standard representation `n! = 1 * 2 * ... * n`. -/
def standardRepresentation (n : ℕ) (i : Fin n) : ℕ := i.1 + 1

def t (n : ℕ) : ℕ := Nat.findGreatest (Feasible n) n.factorial

noncomputable def ratio (n : ℕ) : ℝ := (t n : ℝ) / n

theorem erdos391 :
    Tendsto ratio Filter.atTop (nhds (1 / Real.exp 1)) ∧
      ∃ c : ℝ, 0 < c ∧
        {n : ℕ | ratio n ≤ 1 / Real.exp 1 - c / Real.log n}.Infinite := by
  sorry

end

end Erdos391
