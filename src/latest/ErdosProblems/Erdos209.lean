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
Erdős Problem 209. Informal author: Juan García Escudero.
Formal author: AxiomProver. Published by Axiom Math.
Source: https://www.erdosproblems.com/forum/thread/209#post-7065
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos209/solution.lean
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos209.Proof

namespace Erdos209

theorem not_erdos_209 :
    ∀ d : ℕ, 4 ≤ d → ∃ A : LineArrangement,
      A.card = d ∧ A.pairwiseNonParallel ∧
      (∀ p : PlanePoint, A.pointMultiplicity p ≤ 3) ∧
      ¬∃ L₁ L₂ L₃, A.IsGallaiTriangle L₁ L₂ L₃ := by
  exact erdos_problem_209_disproof

#print axioms not_erdos_209
-- 'Erdos209.not_erdos_209' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos209
