import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Defs

attribute [local instance] Classical.propDecidable

theorem Erdos541.erdos_541 :
    ∀ (p : Nat),
      Fact (Nat.Prime p) →
        ∀ (a : Fin p → ZMod p),
          (@Exists.{1} Nat fun (r : Nat) ↦
              ∀ (S : Finset.{0} (Fin p)),
                @Ne.{1} (Finset.{0} (Fin p)) S
                    (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin p))
                      (@Finset.instEmptyCollection.{0} (Fin p))) →
                  @Eq.{1} (ZMod p)
                      (@Finset.sum.{0, 0} (Fin p) (ZMod p)
                        (@Semiring.toAddCommMonoid.{0} (ZMod p)
                          (@CommSemiring.toSemiring.{0} (ZMod p)
                            (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p))))
                        S fun (i : Fin p) ↦ a i)
                      (@OfNat.ofNat.{0} (ZMod p) (nat_lit 0)
                        (@Zero.toOfNat0.{0} (ZMod p)
                          (@MulZeroClass.toZero.{0} (ZMod p)
                            (@instMulZeroClassOfSemiring.{0} (ZMod p)
                              (@CommSemiring.toSemiring.{0} (ZMod p)
                                (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p))))))) →
                    @Eq.{1} Nat (@Finset.card.{0} (Fin p) S) r) →
            @LE.le.{0} Nat instLENat (@Set.ncard.{0} (ZMod p) (@Set.range.{0, 1} (ZMod p) (Fin p) a))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
  := by
  sorry
