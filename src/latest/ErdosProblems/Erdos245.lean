/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 245.
https://www.erdosproblems.com/forum/thread/245

Informal authors:
- Gregory Freiman

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos245.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/245.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos245.Core

/-!
# Erdős Problem 245

Freiman's affirmative solution: an infinite set of natural numbers of
asymptotic density zero has upper limiting restricted sumset/count ratio at
least three.

The detailed mathematical proof and the Leanization plan are in
`tex/245.tex`.  The imported development proves the quantitative finite
ingredients (the stopping-scale lemma, the proper-GAP diameter bound, and the
sharp `3k - 4` inverse step) before assembling the exact real-cutoff statement
below.
-/

open Filter Set
open scoped Pointwise Topology

namespace Erdos245

/-- The affirmative resolution of Erdős Problem 245. -/
theorem erdos_245 :
    ∀ (A : Set ℕ), A.Infinite →
      atTop.Tendsto
        (fun N ↦ (A ∩ Icc 1 ⌊N⌋₊ |>.ncard : ℝ) / N) (nhds 0) →
      3 ≤ atTop.limsup
        fun N : ℝ ↦ ((A + A) ∩ Icc 1 ⌊N⌋₊ |>.ncard : EReal) /
          (A ∩ Icc 1 ⌊N⌋₊).ncard := by
  exact Erdos245Scratch.erdos_245

#print axioms Erdos245.erdos_245

end Erdos245
