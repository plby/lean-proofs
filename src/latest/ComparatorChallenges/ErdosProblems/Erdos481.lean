import Mathlib.Data.Real.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos481.C :
    {r : Nat} → (Fin r → PNat) → Real
  := by
  sorry

noncomputable def Erdos481.A :
    {r : Nat} → (Fin r → PNat) → (Fin r → PNat) → Nat → List.{0} PNat
  := by
  sorry

theorem Erdos481.erdos_481 :
    ∀ {r : Nat} (a b : Fin r → PNat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Erdos481.C r a) →
          @Exists.{1} Nat fun (k : Nat) ↦
            And
              (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
              (Not (@List.Nodup.{0} PNat (@Erdos481.A r a b k)))
  := by
  sorry
