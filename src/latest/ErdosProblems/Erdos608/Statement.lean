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
/-
Erdős Problem 608.
Informal authors: Zoltán Füredi, Zeinab Maleki; construction described by
Andrzej Grzesik, Ping Hu, and Jan Volec.
Formal authors: Claude Fable 5, Emerson Hsieh.
Source: https://github.com/teorth/erdosproblems/pull/365
https://github.com/primateria/erdos608/tree/b50849234b8de6cb5c642b5cb0479cab2e9e9908
Original Lean version: 4.27.0.
Original Mathlib revision: a3a10db0e9d66acbebf76c5e6a135066525ac900 (v4.27.0).
-/
import Mathlib

set_option linter.mathlibStandardSet false

/-
Erdős problem 608 — statement (Phase-2 target #1).

Site statement (https://www.erdosproblems.com/608, last edited 2025-10-25):
"Let G be a graph with n vertices and > n²/4 many edges. Are there at least
(2/9)n² edges of G which are contained in a C₅?"

DISPROVED by the Füredi–Maleki construction, described in Grzesik–Hu–Volec,
"Minimum number of edges that occur in odd cycles" (arXiv:1605.09055): graphs
with > n²/4 edges and at most ((2+√2)/16)n² + O(n) pentagonal edges.

Design notes in STATEMENT.md alongside this file. All inequalities are cleared
to naturals; the vertex type is `Fin n`.
-/

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

/-- Erdős 608 in its intended (implicitly asymptotic) reading, denominators
cleared: for all sufficiently large `n`, every graph on `n` vertices with
more than `n²/4` edges has at least `(2/9)n²` edges contained in a `C₅`.
(This is the DISPROVED conjecture.)

The word-for-word `∀ n` reading is deliberately NOT used: it is degenerately
false at `n = 3` (`K₃` has `> 9/4` edges and no possible pentagon), which
would let a vacuous two-line proof "disprove" the problem. The eventually-form
below is the reading under which the site's DISPROVED verdict cites the
Füredi–Maleki construction. See STATEMENT.md §Design decisions. -/
def Conjecture : Prop :=
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
    n ^ 2 < 4 * G.edgeSet.ncard → 2 * n ^ 2 ≤ 9 * (pentEdges G).ncard

/-
The campaign targets `disproof : ¬ Conjecture` and `strong_disproof` are
PROVED in `Erdos608/Main.lean` (statement bodies identical to the stubs
originally frozen here; stubs retired 2026-07-29 with Morris's approval —
see runs/phase2/erdos-608/{STATEMENT.md,CONSTRUCTION.md}).
-/

/-- Non-vacuity: in `K₅` the edge `{0, 1}` lies on a pentagon. -/
example : OnC5 (⊤ : SimpleGraph (Fin 5)) s((0 : Fin 5), 1) := by
  unfold OnC5; decide

end Erdos608
