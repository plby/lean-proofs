import Mathlib.Analysis.SpecialFunctions.Log.Base

attribute [local instance] Classical.propDecidable

noncomputable def Erdos497.A :
    Nat → Nat
  := by
  sorry

theorem Erdos497.erdos_497 :
    @Asymptotics.IsEquivalent.{0, 0} Nat Real
      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (fun (n : Nat) ↦
        Real.logb
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@Nat.cast.{0} Real Real.instNatCast (Erdos497.A n)))
      fun (n : Nat) ↦
      @Nat.cast.{0} Real Real.instNatCast
        (n.choose
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  := by
  sorry
