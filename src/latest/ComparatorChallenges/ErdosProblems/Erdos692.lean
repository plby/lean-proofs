attribute [local instance] Classical.propDecidable

noncomputable def Erdos692.delta1 :
    Nat → Nat → Rat
  := by
  sorry

theorem Erdos692.delta1_not_unimodal :
    And
      (@LT.lt.{0} Rat Rat.instLT
        (Erdos692.delta1 (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
        (Erdos692.delta1 (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
      (@LT.lt.{0} Rat Rat.instLT
        (Erdos692.delta1 (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
        (Erdos692.delta1 (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
  := by
  sorry
