/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

set_option linter.style.setOption false
set_option aesop.warn.nonterminal false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

namespace Erdos264

def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  ∀ b : ℕ → ℕ,
    BddAbove (Set.range b) →
      0 ∉ Set.range (a + b) →
        0 ∉ Set.range b →
          Irrational (∑' n, (1 : ℝ) / (a n + b n))
noncomputable section AristotleLemmas

end AristotleLemmas

noncomputable section AristotleLemmas

end AristotleLemmas

end Erdos264

namespace Erdos264

open scoped Classical in
theorem erdos_264.parts.i : ¬IsIrrationalitySequence (2 ^ ·) := by
  sorry

open scoped Classical in
theorem erdos_264.variants.example : IsIrrationalitySequence (fun n ↦ 2 ^ (2 ^ n)) := by
  sorry

end Erdos264
