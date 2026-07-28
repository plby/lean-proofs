import Mathlib.Algebra.BigOperators.Group.Finset.Defs

attribute [local instance] Classical.propDecidable

theorem Erdos532.erdos532 :
    ∀ (c : Nat → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
      @Exists.{1} (Set.{0} Nat) fun (A : Set.{0} Nat) ↦
        And (@Set.Infinite.{0} Nat A)
          (@Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            fun (color : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
            ∀ (S : Finset.{0} Nat),
              @Finset.Nonempty.{0} Nat S →
                @LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat)
                    (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) S) A →
                  @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (c (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid S fun (n : Nat) ↦ n)) color)
  := by
  sorry
