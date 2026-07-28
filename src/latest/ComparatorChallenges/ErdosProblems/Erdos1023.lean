import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Real.Sqrt

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1023.MaxUnionFreeMany :
    Nat → Nat
  := by
  sorry

theorem Erdos1023.erdos_1023 :
    @Exists.{1} Real fun (c : Real) ↦
      And
        (@LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
        (@Asymptotics.IsEquivalent.{0, 0} Nat Real
          (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
            (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
              (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
          (fun (n : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (Erdos1023.MaxUnionFreeMany n))
          fun (n : Nat) ↦
          @HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat
                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                n))
            (@Nat.cast.{0} Real Real.instNatCast n).sqrt)
  := by
  sorry
