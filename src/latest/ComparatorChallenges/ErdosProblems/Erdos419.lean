import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos419

noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card
noncomputable def u (n : ℕ) : ℝ := (tau (n + 1).factorial : ℝ) / (tau n.factorial : ℝ)
def S : Set ℝ := {1} ∪ {x | ∃ k : ℕ, k ≥ 1 ∧ x = 1 + 1 / (k : ℝ)}
end Erdos419

attribute [local instance] Classical.propDecidable

theorem Erdos419.erdos_419 :
    @Eq.{1} (Set.{0} Real)
      (@setOf.{0} Real fun (x : Real) ↦
        @MapClusterPt.{0, 0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          Nat x (@Filter.atTop.{0} Nat Nat.instPreorder) Erdos419.u)
      Erdos419.S
  := by
  sorry
