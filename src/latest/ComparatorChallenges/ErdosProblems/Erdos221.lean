import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

theorem Erdos221.thm_main :
    @Exists.{1} (Set.{0} Nat) fun (A : Set.{0} Nat) ↦
      And
        (@Exists.{1} Real fun (c : Real) ↦
          And
            (@GT.gt.{0} Real Real.instLT c
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
            (@Exists.{1} Nat fun (x₀ : Nat) ↦
              ∀ (x : Nat),
                @GE.ge.{0} Nat instLENat x x₀ →
                  @LE.le.{0} Real Real.instLE
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Set.ncard.{0} Nat
                        (@Set.ofPred.{0} Nat fun (a : Nat) ↦
                          And
                            (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A a)
                            (@LE.le.{0} Nat instLENat a x))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                        (@Nat.cast.{0} Real Real.instNatCast x))
                      (Real.log (@Nat.cast.{0} Real Real.instNatCast x)))))
        (@Exists.{1} Nat fun (N₀ : Nat) ↦
          ∀ (N : Nat),
            @GE.ge.{0} Nat instLENat N N₀ →
              @Exists.{1} Nat fun (k : Nat) ↦
                @Exists.{1} Nat fun (a : Nat) ↦
                  And
                    (@GE.ge.{0} Nat instLENat k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A a)
                      (@Eq.{1} Nat N
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat
                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
                          a))))
  := by
  sorry
