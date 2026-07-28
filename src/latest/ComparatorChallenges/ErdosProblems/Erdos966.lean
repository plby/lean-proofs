import Mathlib.Data.Set.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos966.HasAP :
    Set.{0} Nat → Nat → Prop
  := by
  sorry

noncomputable def Erdos966.HasMonochromaticAP :
    Set.{0} Nat → Nat → {r : Nat} → (Nat → Fin r) → Prop
  := by
  sorry

theorem Erdos966.existence_of_AP_free_Ramsey_set :
    ∀ (k r : Nat),
      @GE.ge.{0} Nat instLENat k (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @GE.ge.{0} Nat instLENat r (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          @Exists.{1} (Set.{0} Nat) fun (A : Set.{0} Nat) ↦
            And
              (Not
                (Erdos966.HasAP A
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (∀ (c : Nat → Fin r), @Erdos966.HasMonochromaticAP A k r c)
  := by
  sorry
