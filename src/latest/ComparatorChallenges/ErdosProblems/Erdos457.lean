import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos457

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable def A_func (n k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)
noncomputable def F (n : ℕ) : ℕ := A_func n ⌊Real.log n⌋₊
end Erdos457

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos457.thm_main :
    @Set.Infinite.{0} Nat
      (@setOf.{0} Nat fun (n : Nat) ↦
        ∀ (p : Nat),
          Nat.Prime p →
            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast p)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfScientific.ofScientific.{0} Real
                    (@NNRatCast.toOfScientific.{0} Real Real.instNNRatCast) (nat_lit 21) Bool.true
                    (nat_lit 1))
                  (Real.log (@Nat.cast.{0} Real Real.instNatCast n))) →
              @Dvd.dvd.{0} Nat Nat.instDvd p (Erdos457.F n))
  := by
  sorry
theorem Erdos457.erdos_457 :
    @Exists.{1} Real fun (ε : Real) ↦
      And
        (@GT.gt.{0} Real Real.instLT ε
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (@Set.Infinite.{0} Nat
          (@setOf.{0} Nat fun (n : Nat) ↦
            ∀ (p : Nat),
              @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast p)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      ε)
                    (Real.log (@Nat.cast.{0} Real Real.instNatCast n))) →
                Nat.Prime p →
                  @Dvd.dvd.{0} Nat Nat.instDvd p
                    (@Finset.prod.{0, 0} Nat Nat Nat.instCommMonoid
                      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                          (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                            Real.instFloorRing)
                          (Real.log (@Nat.cast.{0} Real Real.instNatCast n))))
                      fun (i : Nat) ↦
                      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n i)))
  := by
  sorry
