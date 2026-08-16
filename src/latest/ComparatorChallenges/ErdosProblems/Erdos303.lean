import Mathlib

attribute [local instance] Classical.propDecidable

namespace Erdos303

theorem erdos_303 :
  (∀ (𝓒 : ℤ → ℤ), (Set.range 𝓒).Finite →
    ∃ (a b c : ℤ),
    [a, b, c, 0].Nodup ∧
    (1/a : ℝ) = 1/b + 1/c ∧
    (𝓒 '' {a, b, c}).Subsingleton) := by
  sorry

end Erdos303
