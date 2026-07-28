import Mathlib.Data.Nat.Basic
import Mathlib.Order.Monotone.Defs

attribute [local instance] Classical.propDecidable

universe u_2

noncomputable def Erdos26.IsThick :
    {ι : Type u_2} → (ι → Nat) → Prop
  := by
  let _ := ULift.{u_2, 0} PUnit
  sorry

noncomputable def Erdos26.IsBehrend :
    {ι : Type u_2} → (ι → Nat) → Prop
  := by
  let _ := ULift.{u_2, 0} PUnit
  sorry

theorem Erdos26.erdos_26.variants.rusza :
    @Exists.{1} (Nat → Nat) fun (A : Nat → Nat) ↦
      And (@StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder A)
        (And (Not (@Erdos26.IsThick.{0} Nat A))
          (∀ (k : Nat),
            Not
              (@Erdos26.IsBehrend.{0} Nat fun (x : Nat) ↦
                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (A x) k)))
  := by
  sorry
