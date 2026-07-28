import Mathlib.Data.ENat.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Algebra.Group.Nat.Defs

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos198.IsSidon :
    Set.{0} Nat → Prop
  := by
  sorry

noncomputable def Erdos198.IsAPOfLength :
    {α : Type u_1} → [AddCommMonoid.{u_1} α] → Set.{u_1} α → ENat → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos198.erdos_198 :
    Iff
      (∀ (A : Set.{0} Nat),
        Erdos198.IsSidon A →
          @Exists.{1} (Set.{0} Nat) fun (Y : Set.{0} Nat) ↦
            And (@Erdos198.IsAPOfLength.{0} Nat Nat.instAddCommMonoid Y (@Top.top.{0} ENat instTopENat))
              (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat) Y
                (@Compl.compl.{0} (Set.{0} Nat) (@Set.instCompl.{0} Nat) A)))
      False
  := by
  sorry
