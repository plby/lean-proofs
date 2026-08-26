/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

namespace Erdos464

/-- An irrational multiple of a lacunary sequence stays away from the integers. -/
theorem erdos_464
    (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 0 < a 0)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hlac : ∀ k, (1 + ε₀) * (a k : ℝ) ≤ a (k + 1)) :
    ∃ θ : ℝ, Irrational θ ∧
      (0 : ℝ) ∉ closure
        (Set.range (fun k : ℕ => |θ * (a k : ℝ) - (round (θ * (a k : ℝ)) : ℝ)|)) := by
  sorry

end Erdos464
