import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Pow.Real

attribute [local instance] Classical.propDecidable

noncomputable def Erdos618.maxDegreeFin :
    {n : Nat} → SimpleGraph.{0} (Fin n) → Nat
  := by
  sorry

noncomputable def Erdos618.h2 :
    {n : Nat} → SimpleGraph.{0} (Fin n) → Nat
  := by
  sorry

theorem Erdos618.erdos_618 :
    ∀ (G : (n : Nat) → SimpleGraph.{0} (Fin n)),
      (∀ (n : Nat),
          @SimpleGraph.CliqueFree.{0} (Fin n) (G n)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
        (@Asymptotics.IsLittleO.{0, 0, 0} Nat Real Real Real.norm Real.norm
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (fun (n : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (@Erdos618.maxDegreeFin n (G n)))
            fun (n : Nat) ↦
            (@Nat.cast.{0} Real Real.instNatCast n).rpow
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
          @Asymptotics.IsLittleO.{0, 0, 0} Nat Real Real Real.norm Real.norm
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (fun (n : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (@Erdos618.h2 n (G n))) fun (n : Nat) ↦
            @HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat
                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast n)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
  := by
  sorry
