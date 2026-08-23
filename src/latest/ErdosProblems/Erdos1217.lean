/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1217.
https://www.erdosproblems.com/forum/thread/1217

Informal authors:
- Boris Alexeev
- Kevin Barreto
- Yuchen Li
- Jared Duker Lichtman
- Lisa Price
- J. I. Shah
- Q. Tang
- Terence Tao
- GPT-5.4 Pro

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1217.md
-/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1217.Resolution

/-!
# Erdős Problem 1217

Let `a : ℕ → ℕ` be a strictly increasing sequence of positive integers whose
range has positive lower logarithmic density.  We prove that `a` has a strictly
increasing subsequence of indices whose values form a divisibility chain and whose
normalized upper counting rate is at least the normalized doubly harmonic rate of
the original range.

In fact, the proof uses the stronger theorem of Alexeev, Barreto, Li, Lichtman,
Price, Shah, Tang, and Tao: positive doubly harmonic upper rate alone produces a
chain attaining that rate.  The lower logarithmic density assumption is used only
to establish positivity of the doubly harmonic rate.

Source: Theorem 1.6 of Alexeev--Barreto--Li--Lichtman--Price--Shah--Tang--Tao,
*Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond* (2026).
The detailed mathematical proof and Leanization plan are in `tex/1217.tex`.
-/

namespace Erdos1217

/-- The strengthened sequence form of the resolution: positive doubly harmonic
upper rate suffices, without an assumption on lower logarithmic density. -/
theorem exists_divisibility_subsequence_of_weightedRate_pos
    {a : ℕ → ℕ} (ha : StrictMono a)
    (hweighted : 0 < weightedRate (Set.range a)) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      (∀ i, a (n i) ∣ a (n (i + 1))) ∧
      weightedRate (Set.range a) ≤ chainRate (a ∘ n) := by
  obtain ⟨d, hdmono, hdmem, hddiv, hrate⟩ :=
    exists_divisibility_chain_of_weightedRate_pos (A := Set.range a) hweighted
  obtain ⟨n, hnmono, hnd⟩ := exists_strictMono_indices ha hdmem hdmono
  refine ⟨n, hnmono, ?_, ?_⟩
  · intro i
    rw [hnd i, hnd (i + 1)]
    exact hddiv i
  · have hcomp : a ∘ n = d := by
      funext i
      exact hnd i
    rw [hcomp]
    exact hrate

/-- The affirmative resolution of Erdős Problem 1217. -/
theorem erdos_1217 :
      ∀ (a : ℕ → ℕ), StrictMono a → (∀ i, 0 < a i) →
        0 < lowerLogDensity (Set.range a) →
        ∃ n : ℕ → ℕ, StrictMono n ∧
          (∀ i, a (n i) ∣ a (n (i + 1))) ∧
          weightedRate (Set.range a) ≤ chainRate (a ∘ n) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _ a ha _hapos hlog
    exact exists_divisibility_subsequence_of_weightedRate_pos ha
      (weightedRate_pos_of_lowerLogDensity_pos hlog)
  · intro _
    trivial

end Erdos1217

#print axioms Erdos1217.erdos_1217
