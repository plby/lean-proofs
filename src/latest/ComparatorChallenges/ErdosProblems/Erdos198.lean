import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos198

open scoped Real
open scoped Nat

def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d
variable {α : Type*} [AddCommMonoid α]

def IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}
def IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, IsAPOfLengthWith s l a d
end Erdos198

attribute [local instance] Classical.propDecidable

universe u_1

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
