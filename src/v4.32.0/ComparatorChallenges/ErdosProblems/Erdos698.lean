import Mathlib.Analysis.Real.Sqrt

attribute [local instance] Classical.propDecidable

theorem Erdos698.binomial_gcd_lower_bound :
    ∀ (n i j : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i →
        @LT.lt.{0} Nat instLTNat i j →
          @LE.le.{0} Nat instLENat j
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            @GT.gt.{0} Real Real.instLT
              (@Nat.cast.{0} Real Real.instNatCast ((n.choose i).gcd (n.choose j)))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat
                      (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    i)
                  (@Nat.cast.{0} Real Real.instNatCast n).sqrt)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    (@Nat.cast.{0} Real Real.instNatCast i))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@Nat.cast.{0} Real Real.instNatCast i)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))).sqrt))
  := by
  sorry
