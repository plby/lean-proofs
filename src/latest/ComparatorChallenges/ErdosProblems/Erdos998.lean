/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 998

The endpoint formulation copied in the problem statement is false.  Kesten's actual theorem
characterizes bounded-remainder intervals by their *length*, not by requiring each endpoint to
belong to the orbit of the irrational rotation.
-/

namespace Erdos998

/-- The number of integers `m` with `1 ≤ m ≤ n` for which `{mα} ∈ [u,v)`.  The index `j` in
`range n` represents `m = j + 1`. -/
noncomputable def countInIco (α u v : ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun j ↦
    u ≤ Int.fract (α * (j + 1 : ℕ)) ∧ Int.fract (α * (j + 1 : ℕ)) < v).card

/-- The literal eventual-`O(1)` condition in the displayed problem. -/
def HasBoundedRemainder (α u v : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |(countInIco α u v n : ℝ) - (n : ℝ) * (v - u)| ≤ C

theorem not_erdos_998 :
    ¬ (∀ α u v : ℝ, Irrational α → 0 ≤ u → u < v → v ≤ 1 →
      Erdos998.HasBoundedRemainder α u v →
        (∃ k : ℤ, u = Int.fract (α * (k : ℝ))) ∧
        (∃ l : ℤ, v = Int.fract (α * (l : ℝ)))) := by
  sorry

end Erdos998
