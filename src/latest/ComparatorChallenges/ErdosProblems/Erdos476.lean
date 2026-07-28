import Mathlib.Algebra.Field.ZMod

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos476.restrictedSumset :
    {R : Type u_1} → [Add.{u_1} R] → [DecidableEq.{u_1 + 1} R] → Finset.{u_1} R → Finset.{u_1} R
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos476.erdos_476 :
    ∀ (p : Nat) [inst : Fact (Nat.Prime p)] (A : Finset.{0} (ZMod p)),
      @GE.ge.{0} Nat instLENat
        (@Finset.card.{0} (ZMod p)
          (@Erdos476.restrictedSumset.{0} (ZMod p)
            (@Distrib.toAdd.{0} (ZMod p)
              (@instDistribOfSemiring.{0} (ZMod p)
                (@DivisionSemiring.toSemiring.{0} (ZMod p)
                  (@Semifield.toDivisionSemiring.{0} (ZMod p)
                    (@Field.toSemifield.{0} (ZMod p) (@ZMod.instField p inst))))))
            (ZMod.decidableEq p) A))
        (@Min.min.{0} Nat instMinNat
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Finset.card.{0} (ZMod p) A))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          p)
  := by
  sorry
