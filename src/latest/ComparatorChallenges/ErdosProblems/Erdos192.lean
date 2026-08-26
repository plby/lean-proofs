import Mathlib

namespace Erdos192

def PositiveUnitWalk {d : ℕ} (p : ℕ → Fin d → ℝ) : Prop :=
  ∀ n, ∃ i : Fin d, ∀ j, p (n + 1) j = p n j + if j = i then 1 else 0

/-- Positive coordinate walks force a nontrivial progression exactly through dimension three. -/
theorem erdos_192 (d : ℕ) :
    (∀ p : ℕ → Fin d → ℝ, PositiveUnitWalk p →
      ∃ x y z : Fin d → ℝ, x ∈ Set.range p ∧ y ∈ Set.range p ∧ z ∈ Set.range p ∧
        x ≠ y ∧ ∀ j, x j + z j = 2 * y j) ↔ d ≤ 3 := by
  sorry

end Erdos192
