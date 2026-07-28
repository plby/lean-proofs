import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs

attribute [local instance] Classical.propDecidable

theorem Erdos178.erdos_178 :
    ∀ (a : Nat → Nat → Nat),
      (∀ (i : Nat), @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder (a i)) →
        @Exists.{1} (Nat → Int) fun (f : Nat → Int) ↦
          And
            (∀ (n : Nat),
              Or (@Eq.{1} Int (f n) (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                (@Eq.{1} Int (f n)
                  (@Neg.neg.{0} Int Int.instNegInt
                    (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
            (∀ (d : Nat),
              @Exists.{1} Nat fun (C : Nat) ↦
                ∀ (m i : Nat),
                  @LT.lt.{0} Nat instLTNat i d →
                    @LE.le.{0} Int Int.instLEInt
                      (@abs.{0} Int instLatticeInt Int.instAddGroup
                        (@Finset.sum.{0, 0} Nat Int Int.instAddCommMonoid (Finset.range m)
                          fun (j : Nat) ↦ f (a i j)))
                      (@Nat.cast.{0} Int instNatCastInt C))
  := by
  sorry
