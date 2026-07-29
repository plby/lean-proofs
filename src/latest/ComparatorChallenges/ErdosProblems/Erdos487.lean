import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos487

open scoped Nat
open Filter

attribute [local instance] Classical.propDecidable

noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N => ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ)) Filter.atTop
end Erdos487

attribute [local instance] Classical.propDecidable

theorem Erdos487.erdos_487 :
    ∀ (A : Set.{0} Nat),
      @GT.gt.{0} Real Real.instLT (Erdos487.lowerDensity A)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Exists.{1} Nat fun (a : Nat) ↦
          And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A a)
            (@Exists.{1} Nat fun (b : Nat) ↦
              And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A b)
                (@Exists.{1} Nat fun (c : Nat) ↦
                  And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A c)
                    (And (@Ne.{1} Nat a b)
                      (And (@Ne.{1} Nat b c) (And (@Ne.{1} Nat a c) (@Eq.{1} Nat (a.lcm b) c))))))
  := by
  sorry
