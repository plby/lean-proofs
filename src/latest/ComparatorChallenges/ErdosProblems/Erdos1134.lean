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

Definitions and statement adapted for this repository.
-/
import Mathlib

namespace Erdos1134

inductive ErdosSetA : ℕ → Prop
  | base : ErdosSetA 1
  | double_plus_one (x : ℕ) : ErdosSetA x → ErdosSetA (2 * x + 1)
  | triple_plus_one (x : ℕ) : ErdosSetA x → ErdosSetA (3 * x + 1)
  | sextuple_plus_one (x : ℕ) : ErdosSetA x → ErdosSetA (6 * x + 1)

noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  Filter.liminf (fun N : ℕ => (Set.ncard (S ∩ Set.Iic N) : ℝ) / (N : ℝ)) Filter.atTop

theorem not_erdos_1134 : ¬ 0 < lowerDensity (Set.ofPred ErdosSetA) := by
  sorry

end Erdos1134
