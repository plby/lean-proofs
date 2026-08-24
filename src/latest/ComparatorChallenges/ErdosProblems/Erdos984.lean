/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos984

def IsMonochromaticAP (color : ℕ → Bool) (a d k : ℕ) : Prop :=
  ∃ b : Bool, ∀ i < k, color (a + i * d) = b

theorem erdos_984 :
    ∃ color : ℕ → Bool, ∀ ε : ℝ, 0 < ε →
      ∃ A : ℝ, 0 < A ∧ ∀ a d k : ℕ,
        0 < a → 0 < d → Erdos984.IsMonochromaticAP color a d k →
          (k : ℝ) ≤ A * (a : ℝ) ^ ε := by
  sorry

end Erdos984
