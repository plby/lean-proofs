attribute [local instance] Classical.propDecidable

noncomputable def Erdos947.IsExactCoveringSystem :
    List.{0} (Prod.{0, 0} Int Nat) → Prop
  := by
  sorry

theorem Erdos947.exact_covering_system_distinct_moduli_impossible :
    ∀ (l : List.{0} (Prod.{0, 0} Int Nat)),
      Erdos947.IsExactCoveringSystem l →
        @List.Pairwise.{0} (Prod.{0, 0} Int Nat)
            (fun (p q : Prod.{0, 0} Int Nat) ↦
              @Ne.{1} Nat (@Prod.snd.{0, 0} Int Nat p) (@Prod.snd.{0, 0} Int Nat q))
            l →
          @GE.ge.{0} Nat instLENat (@List.length.{0} (Prod.{0, 0} Int Nat) l)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            False
  := by
  sorry
