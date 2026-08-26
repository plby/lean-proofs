/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file has been modified for Lean/Mathlib 4.33.0.
-/
import Mathlib

namespace Erdos608

/-- `OnC5 G e`: the edge `e` lies on a pentagon of `G` — there are five
pairwise-distinct vertices, adjacent in cyclic order, such that `e` is one of
the five cycle edges. -/
def OnC5 {V : Type*} (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  ∃ a b c d f : V,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ f ∧ b ≠ c ∧ b ≠ d ∧ b ≠ f ∧ c ≠ d ∧ c ≠ f ∧
    d ≠ f ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d f ∧ G.Adj f a ∧
    (e = s(a, b) ∨ e = s(b, c) ∨ e = s(c, d) ∨ e = s(d, f) ∨ e = s(f, a))

/-- The pentagonal edges of `G`. -/
def pentEdges {V : Type*} (G : SimpleGraph V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | OnC5 G e}

theorem not_erdos_608 :
    ¬ (∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
      n ^ 2 < 4 * G.edgeSet.ncard → 2 * n ^ 2 ≤ 9 * (pentEdges G).ncard) := by
  sorry

end Erdos608
