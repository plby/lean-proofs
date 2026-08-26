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
Erdős Problem 403.
Informal argument: AxiomProver; the historical result is due to Frankl and Lin.
Formal proof: AxiomProver, published by Axiom Math.
Source: https://www.erdosproblems.com/forum/thread/403#post-7067
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos403/solution.lean
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos403.Proof

namespace Erdos403

theorem erdos_403 :
    {p : ℕ × Finset ℕ | (∀ a ∈ p.2, 0 < a) ∧ 2 ^ p.1 = p.2.sum Nat.factorial}.Finite := by
  classical
  let solutions : Finset (ℕ × Finset ℕ) :=
    {(0, {1}), (1, {2}), (3, {2, 3}), (5, {2, 3, 4}), (7, {2, 3, 5})}
  apply solutions.finite_toSet.subset
  rintro ⟨m, s⟩ ⟨hpos, hsum⟩
  have hne : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hsum
  have hclass := (erdos403_complete m s).mp ⟨hne, hpos, hsum⟩
  rcases hclass with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [solutions]

#print axioms erdos403_complete
-- 'Erdos403.erdos403_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms erdos_403
-- 'Erdos403.erdos_403' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos403
