import Mathlib.Analysis.Real.Sqrt

attribute [local instance] Classical.propDecidable

noncomputable def Erdos370.maxPrimeFac :
    Nat → Nat
  := by
  sorry

theorem Erdos370.erdos_370 :
    Iff
      (@Set.Infinite.{0} Nat
        (@setOf.{0} Nat fun (n : Nat) ↦
          And
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (Erdos370.maxPrimeFac n))
              (@Nat.cast.{0} Real Real.instNatCast n).sqrt)
            (@LT.lt.{0} Real Real.instLT
              (@Nat.cast.{0} Real Real.instNatCast
                (Erdos370.maxPrimeFac
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast n)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))).sqrt)))
      True
  := by
  sorry
