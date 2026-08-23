/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 58.
https://www.erdosproblems.com/forum/thread/58

Informal authors:
- András Gyárfás

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos58.md
-/
/-
Copyright 2026 The Lean-Proofs Authors.

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
import ErdosProblems.Erdos58.MainReduction
import ErdosProblems.Erdos58.Structural

/-!
# Erdős Problem 58

If a finite graph has odd cycles of at most `k` different lengths, then its
chromatic number is at most `2 * k + 2`.  Equality holds exactly when the
graph contains a copy of `K_(2*k+2)`.

The upper bound is proved by a depth-first-search coloring argument.  The
equality case uses Gyárfás's structural theorem for vertex-two-connected
graphs, formalized in `ErdosProblems.Erdos58.Structural`.
-/

namespace Erdos58

open scoped SimpleGraph

universe u

/-- **Erdős Problem 58 (Bollobás--Erdős conjecture, Gyárfás's theorem).**

The graph is finite, `oddCycleLengths G` is the set of lengths of its odd
simple cycles, and `⊑` denotes containment of a not-necessarily-induced copy.
-/
theorem erdos_58 {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hk : (oddCycleLengths G).encard ≤ (k : ℕ∞)) :
    G.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) ∧
      (G.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) ↔
        SimpleGraph.completeGraph (Fin (2 * k + 2)) ⊑ G) :=
  erdos_58_from_structural G k Structural.gyarfas_structural hk

#print axioms Erdos58.erdos_58

end Erdos58
