import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option aesop.warn.nonterminal false

namespace Erdos31

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 50000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

section

variable {β : Type*} [Preorder β]

variable (S : Set β) (a b : β)

abbrev Set.interIio (S : Set β) (b : β) : Set β :=
  S ∩ Set.Iio b
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  (Set.interIio (S ∩ A) b).ncard / (Set.interIio A b).ncard
open scoped Topology

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Filter.Tendsto (fun (b : β) => partialDensity S A b) Filter.atTop (𝓝 α)
end

end Erdos31

open scoped Pointwise

attribute [local instance] Classical.propDecidable

universe u_2

theorem Erdos31.erdos_31 :
    ∀ (A : Set.{0} Nat),
      @Set.Infinite.{0} Nat A →
        @Exists.{1} (Set.{0} Nat) fun (B : Set.{0} Nat) ↦
          And
            (@Erdos31.HasDensity.{0} Nat Nat.instPreorder
              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                Nat.instLocallyFiniteOrder Nat.instOrderBot)
              B (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@Set.univ.{0} Nat))
            (@Exists.{1} Nat fun (n0 : Nat) ↦
              ∀ (n : Nat),
                @GE.ge.{0} Nat instLENat n n0 →
                  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                    (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                      (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat)) A B)
                    n)
  := by
  sorry
