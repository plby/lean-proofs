/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 984.
https://www.erdosproblems.com/forum/thread/984

Informal authors:
- Zach Hunter

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos984.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos984.Assembly
import ErdosProblems.Erdos984.HunterFamily

/-!
# Erdős Problem 984

There is a two-coloring of the positive integers for which every
monochromatic arithmetic progression beginning at `a` has length
`O_ε(a^ε)` for every `ε > 0`.

The detailed mathematical proof and Leanization map are in `tex/984.tex`.
-/

namespace Erdos984

/-- The affirmative resolution of Erdős Problem 984. -/
theorem erdos_984 : (∃ color : ℕ → Bool, ∀ ε : ℝ, 0 < ε →
  ∃ A : ℝ, 0 < A ∧ ∀ a d k : ℕ,
    0 < a → 0 < d → Erdos984.IsMonochromaticAP color a d k →
      (k : ℝ) ≤ A * (a : ℝ) ^ ε) :=
  erdos984_of_offDiagonal hunterEventualOffDiagonalData.toOffDiagonalData

#print axioms erdos_984

end Erdos984
