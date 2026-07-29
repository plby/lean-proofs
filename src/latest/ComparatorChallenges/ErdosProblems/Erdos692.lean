import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Rat.Init
import Mathlib.Order.Interval.Finset.Nat

namespace Erdos692

open Finset

def numDivisorsIn (x n m : ℕ) : ℕ :=
  ((Ioo n m).filter (· ∣ x)).card

def countWithOneDivisor (n m L : ℕ) : ℕ :=
  ((Icc 1 L).filter (numDivisorsIn · n m = 1)).card

noncomputable def delta1 (n m : ℕ) : ℚ :=
  countWithOneDivisor n m ((Ioo n m).lcm id) / ((Ioo n m).lcm id)
end Erdos692

attribute [local instance] Classical.propDecidable

theorem Erdos692.delta1_not_unimodal :
    And
      (@LT.lt.{0} Rat Rat.instLT
        (Erdos692.delta1 (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
        (Erdos692.delta1 (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
      (@LT.lt.{0} Rat Rat.instLT
        (Erdos692.delta1 (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
        (Erdos692.delta1 (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
  := by
  sorry
