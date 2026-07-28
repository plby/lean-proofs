import Mathlib.NumberTheory.Divisors

attribute [local instance] Classical.propDecidable

noncomputable def UnitFractions.rec_sum :
    Finset.{0} Nat → Rat
  := by
  sorry

theorem Erdos45.erdos45 :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
        @Exists.{1} Nat fun (nₖ : Nat) ↦
          ∀ (c : Nat → Fin k),
            @Exists.{1} (Finset.{0} Nat) fun (D' : Finset.{0} Nat) ↦
              And
                (@LE.le.{0} (Finset.{0} Nat)
                  (@Preorder.toLE.{0} (Finset.{0} Nat)
                    (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                  D'
                  (@Finset.erase.{0} Nat instDecidableEqNat
                    (@Finset.erase.{0} Nat instDecidableEqNat nₖ.divisors
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    nₖ))
                (And
                  (@Eq.{1} Rat (UnitFractions.rec_sum D')
                    (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                  (@Exists.{1} (Fin k) fun (a : Fin k) ↦
                    ∀ (d : Nat),
                      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                            (@Finset.instSetLike.{0} Nat))
                          D' d →
                        @Eq.{1} (Fin k) (c d) a))
  := by
  sorry
