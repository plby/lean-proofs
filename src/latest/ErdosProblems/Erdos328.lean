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
Erdős Problem 328. The imported C = 2 argument and formal proof are by AxiomProver.
Published by Axiom Math. The stronger historical result is due to Nešetřil and Rödl.
Source: https://www.erdosproblems.com/forum/thread/328#post-7066
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos328/solution.lean
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos328.Proof

namespace Erdos328

theorem not_erdos_328 :
    ¬∀ C : ℕ, 0 < C → ∃ t : ℕ, 0 < t ∧
      ∀ A : Set ℕ, (∀ n : ℕ, additiveRepresentation A n ≤ C) →
        ∃ P : Fin t → Set ℕ, IsPartition A t P ∧
          ∀ i : Fin t, ∀ n : ℕ, additiveRepresentation (P i) n < C := by
  intro h
  obtain ⟨C, hC, hbad⟩ := erdos_problem_328_disproof
  obtain ⟨t, ht, hpart⟩ := h C (by omega)
  obtain ⟨A, hA, hno⟩ := hbad t ht
  obtain ⟨P, hP, hbound⟩ := hpart A hA
  obtain ⟨i, n, hn⟩ := hno P hP
  exact (Nat.not_le_of_lt (hbound i n)) hn

#print axioms not_erdos_328
-- 'Erdos328.not_erdos_328' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos328
