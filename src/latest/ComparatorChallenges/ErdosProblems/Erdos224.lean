import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Nat.Defs

attribute [local instance] Classical.propDecidable

noncomputable abbrev Erdos224.E :
    Nat → Type
  := by
  sorry

noncomputable def Erdos224.ObtuseAt :
    {d : Nat} → Erdos224.E d → Erdos224.E d → Erdos224.E d → Prop
  := by
  sorry

theorem Erdos224.exists_obtuse_of_card_succ_pow_two :
    ∀ {d : Nat} (A : Finset.{0} (Erdos224.E d)),
      @Eq.{1} Nat (@Finset.card.{0} (Erdos224.E d) A)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        @Exists.{1} (Erdos224.E d) fun (x : Erdos224.E d) ↦
          @Exists.{1} (Erdos224.E d) fun (y : Erdos224.E d) ↦
            @Exists.{1} (Erdos224.E d) fun (z : Erdos224.E d) ↦
              And
                (@Membership.mem.{0, 0} (Erdos224.E d) (Finset.{0} (Erdos224.E d))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Erdos224.E d)) (Erdos224.E d)
                    (@Finset.instSetLike.{0} (Erdos224.E d)))
                  A x)
                (And
                  (@Membership.mem.{0, 0} (Erdos224.E d) (Finset.{0} (Erdos224.E d))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Erdos224.E d)) (Erdos224.E d)
                      (@Finset.instSetLike.{0} (Erdos224.E d)))
                    A y)
                  (And
                    (@Membership.mem.{0, 0} (Erdos224.E d) (Finset.{0} (Erdos224.E d))
                      (@SetLike.instMembership.{0, 0} (Finset.{0} (Erdos224.E d)) (Erdos224.E d)
                        (@Finset.instSetLike.{0} (Erdos224.E d)))
                      A z)
                    (And (@Ne.{1} (Erdos224.E d) x y)
                      (And (@Ne.{1} (Erdos224.E d) x z)
                        (And (@Ne.{1} (Erdos224.E d) y z) (@Erdos224.ObtuseAt d x y z))))))
  := by
  sorry
