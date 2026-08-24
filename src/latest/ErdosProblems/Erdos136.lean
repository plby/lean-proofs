/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 136.
https://www.erdosproblems.com/forum/thread/136

Informal authors:
- Patrick Bennett
- Ryan Cushman
- Andrzej Dudek
- Paweł Prałat

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos136.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.ConflictFreeMatching
import ErdosProblems.Erdos136.UpperConstruction

/-!
# Erdős Problem 136

Let `f(n)` be the least number of colours needed to colour the edges of the
complete graph `K_n` so that every four vertices span edges of at least five
different colours.  We prove

`f(n) ~ (5 / 6) n`.

The detailed mathematical proof and Leanization plan are in `tex/136.tex`.
-/

namespace Erdos136

open Filter
open scoped Topology

/-- Erdős Problem 136: the minimum number of colours in a colouring of the
edges of `K_n` for which every `K_4` receives at least five colours has
normalized limit `5 / 6`. -/
theorem erdos_136 :
    Tendsto (fun n : ℕ ↦ (erdos136Fun n : ℝ) / (n : ℝ)) atTop
      (nhds (5 / 6 : ℝ)) := by
  obtain ⟨C, C0, hC, hC0, hinstances⟩ :=
    exists_nonnegative_hasEventualJMCInstances
  exact erdos136Fun_tendsto_of_CFM_and_instances hC hC0
    (specializedCFMTheorem jmConflictBudget four_le_jmConflictBudget)
    hinstances

/-- The equivalent asymptotic formulation `f(n) ~ (5 / 6) n`. -/
theorem erdos136_asymptotic :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ ↦ (erdos136Fun n : ℝ))
      (fun n : ℕ ↦ (5 / 6 : ℝ) * (n : ℝ)) := by
  obtain ⟨C, C0, hC, hC0, hinstances⟩ :=
    exists_nonnegative_hasEventualJMCInstances
  exact erdos136Fun_isEquivalent_of_CFM_and_instances hC hC0
    (specializedCFMTheorem jmConflictBudget four_le_jmConflictBudget)
    hinstances

end Erdos136

alias _root_.Erdos136.erdos136 := _root_.Erdos136.erdos_136
