/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 63.
https://www.erdosproblems.com/forum/thread/63

Informal authors:
- Hong Liu
- Richard Montgomery

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos63.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.Bridges
import ErdosProblems.Erdos63.LiuMontgomery

/-!
# Erdős Problem 63

Every graph of infinite chromatic number contains cycles of length `2 ^ n`
for infinitely many natural-number exponents `n`.

The mathematical proof, quantitative finite theorem, and correspondence with
the supporting Lean modules are documented in `tex/63.tex`.
-/

open Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

universe u

/-- **Erdős Problem 63.**  A graph with infinite chromatic number contains
a cycle of length `2 ^ n` for infinitely many exponents `n`. -/
theorem erdos_63 {V : Type u} (G : SimpleGraph V)
    (hG : G.chromaticNumber = ⊤) :
    Set.Infinite {n : ℕ | HasCycleLength G (2 ^ n)} := by
  exact infinite_powerCycleExponents_of_finitePowerTail
    liuMontgomery_finitePowerTail G hG

end Erdos63

#print axioms Erdos63.erdos_63
