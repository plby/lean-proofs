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

Modified for this repository and Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 1134.
Informal proof: D. J. Crampin and A. J. W. Hilton.
Formal proof: AxiomProver, published by Axiom Math.
Source: https://www.erdosproblems.com/1134#post-7068
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos1134/solution.lean
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
import Mathlib

namespace Erdos1134

inductive ErdosSetA : ℕ → Prop
  | base : ErdosSetA 1
  | double_plus_one (x : ℕ) : ErdosSetA x → ErdosSetA (2 * x + 1)
  | triple_plus_one (x : ℕ) : ErdosSetA x → ErdosSetA (3 * x + 1)
  | sextuple_plus_one (x : ℕ) : ErdosSetA x → ErdosSetA (6 * x + 1)

theorem ErdosSetA.smallest (S : Set ℕ) (h1 : 1 ∈ S)
    (h2 : ∀ x ∈ S, 2 * x + 1 ∈ S)
    (h3 : ∀ x ∈ S, 3 * x + 1 ∈ S)
    (h6 : ∀ x ∈ S, 6 * x + 1 ∈ S) :
    Set.ofPred ErdosSetA ⊆ S := by
  intro n hn
  induction hn with
  | base => exact h1
  | double_plus_one x _ ih => exact h2 x ih
  | triple_plus_one x _ ih => exact h3 x ih
  | sextuple_plus_one x _ ih => exact h6 x ih

theorem ErdosSetA.pos {n : ℕ} (h : ErdosSetA n) : 0 < n := by
  induction h with
  | base => omega
  | double_plus_one x _ ih => omega
  | triple_plus_one x _ ih => omega
  | sextuple_plus_one x _ ih => omega

noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  Filter.liminf (fun N : ℕ => (Set.ncard (S ∩ Set.Iic N) : ℝ) / (N : ℝ)) Filter.atTop

end Erdos1134
