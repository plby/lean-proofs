attribute [local instance] Classical.propDecidable

theorem Erdos645.erdos_645 :
    ∀ (c : Nat → Bool),
      @Exists.{1} Nat fun (x : Nat) ↦
        @Exists.{1} Nat fun (d : Nat) ↦
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x)
            (And (@LT.lt.{0} Nat instLTNat x d)
              (@Exists.{1} Bool fun (C : Bool) ↦
                And (@Eq.{1} Bool (c x) C)
                  (And
                    (@Eq.{1} Bool
                      (c (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x d)) C)
                    (@Eq.{1} Bool
                      (c
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d)))
                      C))))
  := by
  sorry
