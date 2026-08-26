import Mathlib

open Cardinal Ordinal

namespace Erdos118

universe u

def Partition (α β : Ordinal.{u}) (n : ℕ) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ S, red.IsClique S ∧ typeLT S = β) ∨
      ∃ S, blue.IsClique S ∧ #S = n

noncomputable def lambda : Ordinal.{0} := ω ^ (ω ^ (2 : Ordinal))

theorem counterexample_at_five :
    Partition lambda lambda 3 ∧ ¬ Partition lambda lambda 5 := by
  sorry

theorem counterexample_at_six :
    Partition lambda lambda 3 ∧ ¬ Partition lambda lambda 6 := by
  sorry

theorem not_erdos_118 :
    ¬ ∀ α : Ordinal.{0}, Partition α α 3 →
      ∀ n : ℕ, 3 ≤ n → Partition α α n := by
  sorry

end Erdos118
