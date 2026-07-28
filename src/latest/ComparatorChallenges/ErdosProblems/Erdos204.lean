import Mathlib.Data.Int.ModEq

attribute [local instance] Classical.propDecidable

noncomputable def Erdos204.IsCDCovering :
    Nat → Prop
  := by
  sorry

theorem Erdos204.T1 :
    Not (@Exists.{1} Nat fun (n : Nat) ↦ Erdos204.IsCDCovering n)
  := by
  sorry

theorem Erdos204.erdos_204 :
    Not
      (@Exists.{1} Nat fun (n : Nat) ↦
        @Exists.{1} (Nat → Int) fun (a : Nat → Int) ↦
          have D :=
            @setOf.{0} Nat fun (d : Nat) ↦
              And (@Dvd.dvd.{0} Nat Nat.instDvd d n)
                (@GT.gt.{0} Nat instLTNat d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))));
          And
            (∀ (x : Int),
              @Exists.{1} Nat fun (d : Nat) ↦
                And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) D d)
                  ((@Nat.cast.{0} Int instNatCastInt d).ModEq x (a d)))
            (∀ (d : Nat),
              @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) D d →
                ∀ (d' : Nat),
                  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) D d' →
                    @Ne.{1} Nat d d' →
                      (@Exists.{1} Int fun (x : Int) ↦
                          (@Nat.cast.{0} Int instNatCastInt d).ModEq x (a d) →
                            (@Nat.cast.{0} Int instNatCastInt d').ModEq x (a d')) →
                        @Eq.{1} Nat (d.gcd d')
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  := by
  sorry
