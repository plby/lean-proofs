import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1000

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

open scoped BigOperators

open Filter

open Topology

def phiA (n : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 (n k)).filter (fun m =>
      ∀ j ∈ Finset.range k, n k / Nat.gcd m (n k) ≠ n j)).card

noncomputable def cesaroPhi (n : ℕ → ℕ) (N : ℕ) : ℝ :=
  ((N : ℝ)⁻¹) *
    ∑ k ∈ Finset.range N, (phiA n k : ℝ) / (n k : ℝ)
end Erdos1000

attribute [local instance] Classical.propDecidable

theorem Erdos1000.erdos_1000_true :
    @Exists.{1} (Nat → Nat) fun (n : Nat → Nat) ↦
      And (@StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder n)
        (And
          (∀ (k : Nat),
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (n k))
          (@Filter.Tendsto.{0, 0} Nat Real (Erdos1000.cesaroPhi n)
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (@nhds.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))
  := by
  sorry
