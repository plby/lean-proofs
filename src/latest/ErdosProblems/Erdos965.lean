/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 965.
https://www.erdosproblems.com/forum/thread/965

Informal authors:
- Péter Komjáth

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos965.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/965.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos965.FiniteColoring
import ErdosProblems.Erdos965.FiniteMain
import ErdosProblems.Erdos965.HamelTransfer

/-!
# Erdős Problem 965

Komjáth's ZFC finite-union coloring, transferred through a Hamel basis of
`ℝ` over `ℚ`, gives a two-coloring for which every uncountable set has two
distinct pair sums of different colors.  Thus the answer is negative.

The detailed mathematical proof and Leanization map are in `tex/965.tex`.
-/

namespace Erdos965

theorem not_erdos_965 :
    ¬ ∀ f : ℝ → Fin 2, ∃ A : Set ℝ, ¬ A.Countable ∧
      ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A), a ≠ b → c ≠ d →
        f (a + b) = f (c + d) := by
  intro hhom
  obtain ⟨color, hcolor⟩ :=
    exists_bad_real_coloring_of_finset_pair_antiramsey
      supportColor_finset_pair_antiramsey
  obtain ⟨A, hA, hmono⟩ := hhom color
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hne⟩ := hcolor A hA
  exact hne (hmono a ha b hb c hc d hd hab hcd)

end Erdos965

#print axioms Erdos965.not_erdos_965

alias _root_.Erdos965.erdos_965 := _root_.Erdos965.not_erdos_965
