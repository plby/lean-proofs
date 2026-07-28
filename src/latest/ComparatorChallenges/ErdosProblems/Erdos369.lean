import Mathlib.Analysis.SpecialFunctions.Pow.Real

attribute [local instance] Classical.propDecidable

noncomputable def Erdos369.Nat.largestPrimeFactor :
    Nat → Nat
  := by
  sorry

theorem Erdos369.erdos_problem_369 :
    ∀ (ε : Real),
      @LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        ∀ (k : Nat),
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
            @Exists.{1} Nat fun (N₀ : Nat) ↦
              ∀ (N : Nat),
                @LE.le.{0} Nat instLENat N₀ N →
                  @Exists.{1} Nat fun (a : Nat) ↦
                    And
                      (@LE.le.{0} Nat instLENat
                        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) N
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (And (@LE.le.{0} Nat instLENat a N)
                        (And (@LE.le.{0} Nat instLENat k a)
                          (∀ (j : Nat),
                            @LT.lt.{0} Nat instLTNat j k →
                              @LE.le.{0} Real Real.instLE
                                (@Nat.cast.{0} Real Real.instNatCast
                                  (Erdos369.Nat.largestPrimeFactor
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
                                      j)))
                                (@HPow.hPow.{0, 0, 0} Real Real Real
                                  (@instHPow.{0, 0} Real Real Real.instPow)
                                  (@Nat.cast.{0} Real Real.instNatCast
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
                                      j))
                                  ε))))
  := by
  sorry
