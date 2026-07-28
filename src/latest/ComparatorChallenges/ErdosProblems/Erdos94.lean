import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

attribute [local instance] Classical.propDecidable

noncomputable abbrev Erdos94.Point :
    Type
  := by
  sorry

noncomputable def Erdos94.S :
    Finset.{0} Erdos94.Point → Real
  := by
  sorry

noncomputable def Erdos94.NoThreeCollinear :
    Finset.{0} Erdos94.Point → Prop
  := by
  sorry

noncomputable def Erdos94.ConvexPosition :
    Finset.{0} Erdos94.Point → Prop
  := by
  sorry

theorem Erdos94.erdos94_convex_no3collinear :
    ∀ (P : Finset.{0} Erdos94.Point),
      Erdos94.ConvexPosition P →
        Erdos94.NoThreeCollinear P →
          @LE.le.{0} Real Real.instLE (Erdos94.S P)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 4)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Nat.instNeZeroSucc
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat
                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Erdos94.Point P))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Erdos94.Point P))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  := by
  sorry
