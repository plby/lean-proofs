import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace Erdos350

open scoped Real
open scoped Nat

open Finset

def DecidableDistinctSubsetSums {M : Type*} [AddCommMonoid M] [DecidableEq M]
    (A : Finset M) : Prop :=
  ∀ X ⊆ A, ∀ Y ⊆ A, X ≠ Y → X.sum id ≠ Y.sum id
end Erdos350

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos350.erdos_350 :
    ∀ (A : Finset.{0} Nat),
      @Erdos350.DecidableDistinctSubsetSums.{0} Nat Nat.instAddCommMonoid instDecidableEqNat A →
        @LT.lt.{0} Real Real.instLT
          (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid A fun (n : Nat) ↦
            @HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@Nat.cast.{0} Real Real.instNatCast n))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
  := by
  sorry
