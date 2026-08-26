/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
MIT License

Copyright (c) 2026 Axiom Math.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

This file has been modified for Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 231, finite disproof.
Informal authors: Nicolaas Govert de Bruijn, Paul Erdős (as credited by EPC).
Formal author: AxiomProver. Published by Axiom Math.
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos231/solution.lean
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos231.Proof

namespace Erdos231

theorem not_erdos_231 :
    ¬∀ k : ℕ, 2 ≤ k → ∀ S : List (Fin k), S.length = 2 ^ k - 1 →
      ∃ i len : ℕ, 2 ≤ len ∧ i + len ≤ S.length ∧
        IsAbelianSquare ((S.drop i).take len) := by
  intro h
  exact erdos_problem_231_k4.2
    (h 4 (by decide) _ erdos_problem_231_k4.1)

#print axioms not_erdos_231
-- 'Erdos231.not_erdos_231' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos231
