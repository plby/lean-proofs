import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.ModEq
import Mathlib.Order.ConditionallyCompleteLattice.Basic

attribute [local instance] Classical.propDecidable

theorem Erdos275.erdos_275 :
    ∀ (r : Nat) (a : Fin r → Int) (n : Fin r → Nat),
      (@Exists.{1} Int fun (k : Int) ↦
          ∀ (x : Int),
            @Membership.mem.{0, 0} Int (Set.{0} Int) (@Set.instMembership.{0} Int)
                (@Set.Ico.{0} Int
                  (@PartialOrder.toPreorder.{0} Int
                    (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0} Int
                      (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0} Int
                        (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0} Int
                          (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Int
                            Int.instConditionallyCompleteLinearOrder)))))
                  k
                  (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) k
                    (@HPow.hPow.{0, 0, 0} Int Nat Int
                      (@instHPow.{0, 0} Int Nat
                        (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) r)))
                x →
              @Exists.{1} (Fin r) fun (i : Fin r) ↦
                (@Nat.cast.{0} Int instNatCastInt (n i)).ModEq x (a i)) →
        ∀ (x : Int),
          @Exists.{1} (Fin r) fun (i : Fin r) ↦ (@Nat.cast.{0} Int instNatCastInt (n i)).ModEq x (a i)
  := by
  sorry
