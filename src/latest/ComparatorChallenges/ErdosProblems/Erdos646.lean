import Mathlib.Algebra.Field.ZMod

attribute [local instance] Classical.propDecidable

noncomputable def Erdos646.partial_sum :
    (k : Nat) →
      (Fin k → Nat) → Nat → Fin k → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
  := by
  sorry

theorem Erdos646.infinitely_many_even_factorial_exponents :
    ∀ (k : Nat) (p : Fin k → Nat),
      (∀ (i : Fin k), Nat.Prime (p i)) →
        @Function.Injective.{1, 1} (Fin k) Nat p →
          @Set.Infinite.{0} Nat
            (@setOf.{0} Nat fun (n : Nat) ↦
              ∀ (i : Fin k),
                @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Erdos646.partial_sum k p n i)
                  (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (nat_lit 0)
                    (@Zero.toOfNat0.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@MulZeroClass.toZero.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@instMulZeroClassOfSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@DivisionSemiring.toSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Semifield.toDivisionSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Field.toSemifield.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@ZMod.instField
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  Nat.fact_prime_two)))))))))
  := by
  sorry
