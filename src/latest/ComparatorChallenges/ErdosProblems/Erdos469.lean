import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Erdos469

def Nat.IsSumDivisors (n : ℕ) : Prop :=
  ∃ S ⊆ n.properDivisors, ∑ d ∈ S, d = n

open Erdos469

theorem erdos_469 :
    letI A := {n : ℕ | 0 < n ∧ n.IsSumDivisors ∧
      ∀ m < n, m ∣ n → ¬m.IsSumDivisors}
    Summable fun n : A ↦ 1 / (n : ℝ) := by
  sorry

end Erdos469
