import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Group.Pointwise.Set.Basic

open scoped Pointwise

attribute [local instance] Classical.propDecidable

universe u_2

noncomputable def Erdos31.HasDensity :
    {β : Type u_2} →
      [inst : Preorder.{u_2} β] →
        [@LocallyFiniteOrderBot.{u_2} β inst] →
          Set.{u_2} β → Real → optParam.{u_2 + 1} (Set.{u_2} β) (@Set.univ.{u_2} β) → Prop
  := by
  let _ := ULift.{u_2, 0} PUnit
  sorry

theorem Erdos31.erdos_31 :
    ∀ (A : Set.{0} Nat),
      @Set.Infinite.{0} Nat A →
        @Exists.{1} (Set.{0} Nat) fun (B : Set.{0} Nat) ↦
          And
            (@Erdos31.HasDensity.{0} Nat Nat.instPreorder
              (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
                Nat.instLocallyFiniteOrder Nat.instOrderBot)
              B (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@Set.univ.{0} Nat))
            (@Exists.{1} Nat fun (n0 : Nat) ↦
              ∀ (n : Nat),
                @GE.ge.{0} Nat instLENat n n0 →
                  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                    (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                      (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat)) A B)
                    n)
  := by
  sorry
