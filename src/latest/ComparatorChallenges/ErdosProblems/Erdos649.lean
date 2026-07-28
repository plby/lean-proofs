import Mathlib.Data.Finite.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos649.StrangePair :
    Nat → Nat → Prop
  := by
  sorry

theorem Erdos649.infinite_strange_pairs :
    @Set.Infinite.{0} Nat
      (@setOf.{0} Nat fun (q : Nat) ↦
        Erdos649.StrangePair (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q)
  := by
  sorry
