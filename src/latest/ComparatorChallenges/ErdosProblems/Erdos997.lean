import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Defs

attribute [local instance] Classical.propDecidable

axiom maynardTaoBFT :
    ∀ (m : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
        @Exists.{1} Nat fun (C : Nat) ↦
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) C)
            (∀ (q : Nat),
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
                ∀ (a : Int),
                  @Eq.{1} Nat (a.gcd (@Nat.cast.{0} Int instNatCastInt q))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                    ∀ (N : Nat),
                      @Exists.{1} Nat fun (r : Nat) ↦
                        And (@LE.le.{0} Nat instLENat N r)
                          (And
                            (∀ (j : Nat),
                              @LT.lt.{0} Nat instLTNat j m →
                                (@Nat.cast.{0} Int instNatCastInt q).ModEq
                                  (@Nat.cast.{0} Int instNatCastInt
                                    (Nat.nth Nat.Prime
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                        j)))
                                  a)
                            (@LE.le.{0} Nat instLENat
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (Nat.nth Nat.Prime
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                      m)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (Nat.nth Nat.Prime r))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q C))))

noncomputable def Erdos997.fracSeq :
    Real → Nat → Real
  := by
  sorry

noncomputable def Erdos997.IsWellDistributed :
    (Nat → Real) → Prop
  := by
  sorry

theorem Erdos997.erdos997 :
    ∀ (α : Real), Not (Erdos997.IsWellDistributed (Erdos997.fracSeq α))
  := by
  sorry
