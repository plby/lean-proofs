import Mathlib.Combinatorics.Additive.SubsetSum
import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Erdos469

/-- A positive integer is semiperfect if it is a sum of distinct proper divisors. -/
def Semiperfect (n : ℕ) : Prop :=
  0 < n ∧ n ∈ n.properDivisors.subsetSum

/-- A semiperfect integer with no semiperfect proper divisor. -/
def PrimitiveSemiperfect (n : ℕ) : Prop :=
  Semiperfect n ∧ ∀ d ∈ n.properDivisors, ¬Semiperfect d

/-- Erdős Problem 469: the reciprocal function is summable on primitive
semiperfect positive integers. -/
theorem erdos469 :
    Summable (fun N : {N : Nat // PrimitiveSemiperfect N} =>
      (N.1 : Real)⁻¹) := by
  sorry

end Erdos469
