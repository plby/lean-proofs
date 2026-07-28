import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Defs

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def UnitFractions.rec_sum :
    Finset.{0} Nat → Rat
  := by
  sorry

theorem Erdos46.erdos46 :
    ∀ {α : Type u_1} [Finite.{u_1 + 1} α] (c : Int → α),
      @Exists.{1} (Finset.{0} Nat) fun (S : Finset.{0} Nat) ↦
        And
          (∀ (n : Nat),
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S
                n →
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
          (And
            (@Eq.{1} Rat (UnitFractions.rec_sum S)
              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (@Exists.{u_1 + 1} α fun (a : α) ↦
              ∀ (n : Nat),
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    S n →
                  @Eq.{u_1 + 1} α (c (@Nat.cast.{0} Int instNatCastInt n)) a))
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry
