/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Cardinal

namespace Erdos1127

def HasDistinctOrientedPairDistances {X : Type*} [PseudoMetricSpace X]
    (color : X → ℕ) : Prop :=
  ∀ ⦃x y u v : X⦄,
    color x = color y →
    color x = color u →
    color x = color v →
    x ≠ y → u ≠ v →
    dist x y = dist u v →
    x = u ∧ y = v

def HasDistinctIncludingDegeneratePairs {X : Type*} [PseudoMetricSpace X]
    (color : X → ℕ) : Prop :=
  ∀ ⦃x y u v : X⦄,
    color x = color y →
    color x = color u →
    color x = color v →
    dist x y = dist u v →
    (x = u ∧ y = v) ∨ (x = v ∧ y = u)

def HasDistinctPairDistances {X : Type*} [PseudoMetricSpace X]
    (color : X → ℕ) : Prop :=
  ∀ ⦃x y u v : X⦄,
    color x = color y →
    color x = color u →
    color x = color v →
    x ≠ y → u ≠ v →
    dist x y = dist u v →
    (x = u ∧ y = v) ∨ (x = v ∧ y = u)

theorem erdos_1127_oriented_pair_formulation_false :
    ¬ ∃ color : ℝ → ℕ, HasDistinctOrientedPairDistances color := by
  sorry

theorem erdos_1127_degenerate_pair_formulation_false :
    ¬ ∃ color : ℝ → ℕ, HasDistinctIncludingDegeneratePairs color := by
  sorry

theorem erdos_1127 :
    (𝔠 = (ℵ_ 1 : Cardinal.{0})) ↔ (∀ n : ℕ, ∃ color : EuclideanSpace ℝ (Fin n) → ℕ,
      Erdos1127.HasDistinctPairDistances color) := by
  sorry

end Erdos1127
