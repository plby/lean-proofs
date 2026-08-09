import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos347

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

set_option relaxedAutoImplicit false
set_option autoImplicit false

def has_asymptotic_density_one (S : Set ℕ) : Prop :=
  Filter.Tendsto (fun n => ((Finset.range n).filter (· ∈ S)).card / (n : ℝ)) Filter.atTop (nhds 1)
def subset_sums_of_set (S : Set ℕ) : Set ℕ :=
  {s | ∃ (B : Finset ℕ), (∀ x ∈ B, x ∈ S) ∧ s = B.sum id}
end Erdos347

attribute [local instance] Classical.propDecidable

theorem Erdos347.answer_is_yes :
    @Exists.{1} (Nat → Nat) fun (A : Nat → Nat) ↦
      And (@Monotone.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder A)
        (And
          (@Filter.Tendsto.{0, 0} Nat Real
            (fun (n : Nat) ↦
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast
                  (A
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Nat.cast.{0} Real Real.instNatCast (A n)))
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (@nhds.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
          (∀ (S : Set.{0} Nat),
            And (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat) S (@Set.range.{0, 1} Nat Nat A))
                (@Set.Finite.{0} Nat
                  (@SDiff.sdiff.{0} (Set.{0} Nat) (@Set.instSDiff.{0} Nat) (@Set.range.{0, 1} Nat Nat A)
                    S)) →
              Erdos347.has_asymptotic_density_one (Erdos347.subset_sums_of_set S)))
  := by
  sorry
