/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 294.
https://www.erdosproblems.com/forum/thread/294

Informal authors:
- Yang P. Liu
- Mehtaab Sawhney

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos294.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos294.SharpLower
import ErdosProblems.Erdos294.Upper

/-!
# Erdős Problem 294

For `N ≥ 1`, let `t(N)` be the least positive integer `t` for which `1`
cannot be written as a sum of distinct unit fractions with least denominator
`t` and largest denominator at most `N`.  Liu and Sawhney proved

`N / (log N * (log log N)^3 * (log log log N)^O(1)) ≪ t(N) ≪ N / log N`.

The detailed mathematical proof and the formalization map are in `tex/294.tex`.
-/

namespace Erdos294

noncomputable section

/-- Resolution of Erdős Problem 294.  The lower bound has the explicit
exponent `20` in place of the source's `(log log log N)^O(1)`; the constants
on both sides are absolute and positive. -/
theorem erdos_294 : (∃ (k : ℕ) (c C : ℝ), 0 < c ∧ 0 < C ∧
  ∀ᶠ N : ℕ in Filter.atTop,
    c * Erdos294.lowerProfile k N ≤ Erdos294.firstForbidden N ∧
      (Erdos294.firstForbidden N : ℝ) ≤ C * Erdos294.upperProfile N) := by
  obtain ⟨k, c, hc, hlower⟩ :=
    SharpLower.eventually_lowerProfile_le_firstForbidden
  obtain ⟨C, hC, hupper⟩ := Upper.eventually_firstForbidden_le_upper
  exact ⟨k, c, C, hc, hC, hlower.and hupper⟩

end

end Erdos294

#print axioms Erdos294.erdos_294
