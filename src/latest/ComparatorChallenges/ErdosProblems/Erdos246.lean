import Mathlib.Data.Set.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos246.IsCompleteSeq :
    Set.{0} Nat → Prop
  := by
  sorry

noncomputable def Erdos246.Gamma :
    Nat → Nat → Set.{0} Nat
  := by
  sorry

theorem Erdos246.erdos_246 :
    ∀ (a b : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b →
          a.Coprime b → Erdos246.IsCompleteSeq (Erdos246.Gamma a b)
  := by
  sorry
