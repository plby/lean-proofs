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

This file has been modified.
-/
import Mathlib

namespace Erdos328

noncomputable def additiveRepresentation (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

def IsPartition (A : Set ℕ) (t : ℕ) (P : Fin t → Set ℕ) : Prop :=
  (⋃ i, P i) = A ∧
  Set.PairwiseDisjoint (Set.univ : Set (Fin t)) P

theorem not_erdos_328 :
    ¬∀ C : ℕ, 0 < C → ∃ t : ℕ, 0 < t ∧
      ∀ A : Set ℕ, (∀ n : ℕ, additiveRepresentation A n ≤ C) →
        ∃ P : Fin t → Set ℕ, IsPartition A t P ∧
          ∀ i : Fin t, ∀ n : ℕ, additiveRepresentation (P i) n < C := by
  sorry

end Erdos328
