import Mathlib.Analysis.Asymptotics.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos447.MaxUnionFree :
    Nat → Nat
  := by
  sorry

theorem Erdos447.erdos_447 :
    @Asymptotics.IsEquivalent.{0, 0} Nat Real
      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real
        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Real
          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Real
            (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (fun (n : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (Erdos447.MaxUnionFree n)) fun (n : Nat) ↦
      @Nat.cast.{0} Real Real.instNatCast
        (n.choose
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  := by
  sorry
