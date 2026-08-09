import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace UnitFractions

open scoped BigOperators
open Filter Real Finset Nat
open _root_.Finset

noncomputable section
attribute [local instance] Classical.propDecidable

section

variable (A : Set ℕ)

variable {A}

end

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n
namespace Nat

end Nat

end

end UnitFractions

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos46.erdos46 :
    ∀ {α : Type u_1} [Finite.{u_1 + 1} α] (c : Int → α),
      @Exists.{1} (Finset.{0} Nat) fun (S : Finset.{0} Nat) ↦
        And
          (∀ (n : Nat),
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S
                n →
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
          (And
            (@Eq.{1} Rat (UnitFractions.rec_sum S)
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (@Exists.{u_1 + 1} α fun (a : α) ↦
              ∀ (n : Nat),
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    S n →
                  @Eq.{u_1 + 1} α (c (@Nat.cast.{0} Int instNatCastInt n)) a))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
