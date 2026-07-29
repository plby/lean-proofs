import Mathlib.Algebra.Quotient
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.cases false
set_option linter.style.cdot false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false

open scoped Real
open scoped Nat
open scoped Pointwise

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 2000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Function MulAction
open scoped Pointwise

namespace Finset
variable {ι α : Type*}

local notation s " +ₛ " N => Finset.image ((↑) : α → α ⧸ N) s
local notation s " +ˢ " N => Set.image ((↑) : α → α ⧸ N) s

section Group
variable [Group α] [DecidableEq α] {s t : Finset α} {a : α}

end Group

variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}

end Finset
open Function MulAction
open scoped Pointwise

variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}

namespace Finset

variable (s t)

end Finset
namespace Finset

end Finset

local notation:max "#" s:max => Finset.card s

namespace Erdos433

def S (E : Set ℕ) : AddSubsemigroup ℕ := AddSubsemigroup.closure E
noncomputable def G (E : Set ℕ) : ℕ := sSup {n | n ∉ S E}

noncomputable def g (b a : ℕ) : ℕ :=
  sSup {G E | (E : Finset ℕ)
    (_hE_sub : (E : Set ℕ) ⊆ Set.Icc 1 a)
    (_hE_card : E.card = b)
    (_hE_gcd : Finset.gcd E id = 1)}
end Erdos433

attribute [local instance] Classical.propDecidable

theorem Erdos433.theorem_1 :
    ∀ (a b : Nat),
      @GE.ge.{0} Nat instLENat b (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @LT.lt.{0} Nat instLTNat b a →
          And
            (@LE.le.{0} Int Int.instLEInt
              (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                  (@Int.floor.{0} Real Real.instRing Real.linearOrder Real.instFloorRing
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@Nat.cast.{0} Real Real.instNatCast a)
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@Nat.cast.{0} Real Real.instNatCast b)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                  (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                    (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                      (@Nat.cast.{0} Int instNatCastInt a) (@Nat.cast.{0} Int instNatCastInt b))
                    (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@Nat.cast.{0} Int instNatCastInt (Erdos433.g b a)))
            (@LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (Erdos433.g b a))
              (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                  (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                    (@Int.ceil.{0} Real Real.instRing Real.linearOrder Real.instFloorRing
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@Nat.cast.{0} Real Real.instNatCast a)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@Nat.cast.{0} Real Real.instNatCast b)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                    (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@Nat.cast.{0} Int instNatCastInt a))
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
  := by
  sorry
