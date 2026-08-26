/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Expected root counts on an interval partition indexed by a natural interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.PartitionExpectation

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem integral_intervalRootCount_Ico_identity (n a b : ℕ) (hab : a ≤ b)
    (g : ℕ → ℝ) (hg : Monotone g) :
    (∑ i ∈ Finset.Ico a b, ∫ ε, (intervalRootCount ε n (g i) (g (i + 1)) : ℝ) ∂sequenceLaw) +
        sequenceLaw.real {ε | powerSum ε (n + 1) (g a) = 0} =
      (∫ ε, (intervalRootCount ε n (g a) (g b) : ℝ) ∂sequenceLaw) +
        ∑ i ∈ Finset.Ico a b, sequenceLaw.real {ε | powerSum ε (n + 1) (g i) = 0} := by
  have h := integral_intervalRootCount_grid_identity n (b - a) (fun i ↦ g (a + i))
    (fun i j hij ↦ hg (Nat.add_le_add_left hij a))
  simpa only [Finset.sum_Ico_eq_sum_range, Nat.add_zero, Nat.add_sub_of_le hab, Nat.add_assoc] using h

end Erdos521
