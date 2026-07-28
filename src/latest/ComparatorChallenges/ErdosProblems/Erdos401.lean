import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos401.P :
    Nat → Nat
  := by
  sorry

noncomputable def Erdos401.ω :
    Nat → Real
  := by
  sorry

theorem Erdos401.theorem_1 :
    ∀ (r : Nat),
      @GE.ge.{0} Nat instLENat r (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Set.Infinite.{0} Nat
          (@setOf.{0} Nat fun (n : Nat) ↦
            @Exists.{1} Nat fun (a1 : Nat) ↦
              @Exists.{1} Nat fun (a2 : Nat) ↦
                And
                  (@GT.gt.{0} Nat instLTNat a1
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (And
                    (@GT.gt.{0} Nat instLTNat a2
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (And
                      (@GT.gt.{0} Real Real.instLT
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast a1)
                          (@Nat.cast.{0} Real Real.instNatCast a2))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast n)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (Erdos401.ω r) (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))))
                      (@Dvd.dvd.{0} Nat Nat.instDvd
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a1.factorial
                          a2.factorial)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n.factorial
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat
                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                            (Erdos401.P r) n))))))
  := by
  sorry
