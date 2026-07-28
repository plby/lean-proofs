import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Card

attribute [local instance] Classical.propDecidable

universe u_1 u_2

noncomputable def Set.PairwiseNonCommuting :
    {G : Type u_1} → [Group.{u_1} G] → Set.{u_1} G → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos1098.erdos1098 :
    ∀ (G : Type u_2) [inst : Group.{u_2} G],
      (∀ (S : Set.{u_2} G), @Set.PairwiseNonCommuting.{u_2} G inst S → @Set.Finite.{u_2} G S) →
        @Exists.{1} Nat fun (n : Nat) ↦
          ∀ (S : Finset.{u_2} G),
            @Set.PairwiseNonCommuting.{u_2} G inst
                (@SetLike.coe.{u_2, u_2} (Finset.{u_2} G) G (@Finset.instSetLike.{u_2} G) S) →
              @LE.le.{0} Nat instLENat (@Finset.card.{u_2} G S) n
  := by
  let _ := ULift.{u_2, 0} PUnit
  sorry
