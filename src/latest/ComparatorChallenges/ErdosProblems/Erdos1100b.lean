import Mathlib.Data.Real.Basic

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1100b.tau_perp :
    Nat → Nat
  := by
  sorry

noncomputable def Erdos1100b.PNT_statement :
    Prop
  := by
  sorry

noncomputable def Erdos1100b.bound :
    Nat → Real → Real
  := by
  sorry

theorem Erdos1100b.main_theorem :
    Erdos1100b.PNT_statement →
      ∀ (ε : Real),
        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
            (@Set.Ioo.{0} Real Real.instPreorder
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
            ε →
          ∀ (N : Nat),
            @Exists.{1} Nat fun (n : Nat) ↦
              And (@GE.ge.{0} Nat instLENat n N)
                (@GT.gt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast (Erdos1100b.tau_perp n)) (Erdos1100b.bound n ε))
  := by
  sorry
