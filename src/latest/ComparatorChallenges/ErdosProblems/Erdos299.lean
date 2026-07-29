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

theorem Erdos299.not_erdos299 :
    Not
      (@Exists.{1} (Nat → Nat) fun (a : Nat → Nat) ↦
        And (@StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder a)
          (And
            (∀ (i : Nat),
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (a i))
            (And
              (@Exists.{1} Nat fun (C : Nat) ↦
                ∀ (i : Nat),
                  @LE.le.{0} Nat instLENat
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (a
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (a i))
                    C)
              (∀ (S : Finset.{0} Nat),
                @Ne.{1} Rat
                  (UnitFractions.rec_sum (@Finset.image.{0, 0} Nat Nat instDecidableEqNat a S))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))))
  := by
  sorry
