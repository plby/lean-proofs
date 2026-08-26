import Mathlib

open Cardinal Ordinal

universe u

def OrdinalCardinalRamsey (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
      ∃ s, blue.IsClique s ∧ #s = c

namespace Erdos591

noncomputable abbrev erdos591Ordinal : Ordinal.{0} := ω ^ (ω ^ 2)

theorem erdos_591_counterexample :
    OrdinalCardinalRamsey erdos591Ordinal erdos591Ordinal (3 : Cardinal.{0}) ∧
      ¬ OrdinalCardinalRamsey erdos591Ordinal erdos591Ordinal (6 : Cardinal.{0}) := by
  sorry

theorem not_erdos_591 :
    ¬ ∀ α : Ordinal.{0}, OrdinalCardinalRamsey α α (3 : Cardinal.{0}) →
      ∀ n : ℕ, 3 ≤ n → OrdinalCardinalRamsey α α (n : Cardinal.{0}) := by
  sorry

end Erdos591
