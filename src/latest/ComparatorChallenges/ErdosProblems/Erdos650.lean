import Mathlib.Analysis.Real.Sqrt

attribute [local instance] Classical.propDecidable

noncomputable def Erdos650.erdos_f :
    Nat → Nat
  := by
  sorry

theorem Erdos650.erdos_f_eq :
    ∀ (m : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
        @Eq.{1} Nat (Erdos650.erdos_f m)
          (@Min.min.{0} Nat instMinNat m
            (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
              (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@Nat.cast.{0} Real Real.instNatCast m).sqrt)))
  := by
  sorry
