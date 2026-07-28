import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Filter.AtTopBot.Defs

attribute [local instance] Classical.propDecidable

noncomputable instance Erdos429.instFintypeSetInterIccNat :
    (B : Set.{0} Nat) →
      (a b : Nat) →
        Fintype.{0}
          (@Set.Elem.{0} Nat
            (@Inter.inter.{0} (Set.{0} Nat) (@Set.instInter.{0} Nat) B
              (@Set.Icc.{0} Nat Nat.instPreorder a b)))
  := by
  sorry

noncomputable def Erdos429.Admissible :
    Set.{0} Nat → Prop
  := by
  sorry

theorem Erdos429.main_theorem :
    ∀ (f : Nat → Nat),
      @Filter.Tendsto.{0, 0} Nat Nat f (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@Filter.atTop.{0} Nat Nat.instPreorder) →
        @Exists.{1} (Set.{0} Nat) fun (B : Set.{0} Nat) ↦
          And (@Set.Infinite.{0} Nat B)
            (And
              (∀ (N : Nat),
                @LE.le.{0} Nat instLENat
                  (@Finset.card.{0} Nat
                    (@Set.toFinset.{0} Nat
                      (@Inter.inter.{0} (Set.{0} Nat) (@Set.instInter.{0} Nat) B
                        (@Set.Icc.{0} Nat Nat.instPreorder
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N))
                      (Erdos429.instFintypeSetInterIccNat B
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N)))
                  (f N))
              (And (Erdos429.Admissible B)
                (∀ (n : Int),
                  @Exists.{1} Nat fun (b : Nat) ↦
                    And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) B b)
                      (Not
                        (Nat.Prime
                          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                              (@Nat.cast.{0} Int instNatCastInt b) n).toNat)))))
  := by
  sorry
