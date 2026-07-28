attribute [local instance] Classical.propDecidable

noncomputable def Erdos290.v :
    Nat → Nat → Nat
  := by
  sorry

theorem Erdos290.main :
    ∀ (a : Nat),
      @GT.gt.{0} Nat instLTNat a (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Exists.{1} Nat fun (b : Nat) ↦
          And (@LT.lt.{0} Nat instLTNat a b)
            (And
              (@LE.le.{0} Nat instLENat b
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) a))
              (@LT.lt.{0} Nat instLTNat (Erdos290.v a b)
                (Erdos290.v a
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) b
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
  := by
  sorry
