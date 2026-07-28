import Mathlib.Order.Interval.Finset.Nat

attribute [local instance] Classical.propDecidable

noncomputable def Erdos867.ConsecutiveSumFree :
    Finset.{0} Nat → Prop
  := by
  sorry

theorem Erdos867.construction_19_36 :
    @Exists.{1} Nat fun (C : Nat) ↦
      ∀ (n : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 144) (instOfNatNat (nat_lit 144))) n →
          @Exists.{1} (Finset.{0} Nat) fun (S : Finset.{0} Nat) ↦
            And
              (@LE.le.{0} (Finset.{0} Nat)
                (@Preorder.toLE.{0} (Finset.{0} Nat)
                  (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                S
                (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n))
              (And (Erdos867.ConsecutiveSumFree S)
                (@GE.ge.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36)))
                      (@Finset.card.{0} Nat S))
                    C)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))) n)))
  := by
  sorry

theorem Erdos867.csf_exceeds_half_plus_constant :
    Not
      (@Exists.{1} Nat fun (C : Nat) ↦
        ∀ (n : Nat) (S : Finset.{0} Nat),
          @LE.le.{0} (Finset.{0} Nat)
              (@Preorder.toLE.{0} (Finset.{0} Nat)
                (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
              S
              (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) →
            Erdos867.ConsecutiveSumFree S →
              @LE.le.{0} Nat instLENat
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Finset.card.{0} Nat S))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n C))
  := by
  sorry
