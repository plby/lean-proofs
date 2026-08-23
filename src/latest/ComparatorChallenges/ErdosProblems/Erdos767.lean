/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 767

For positive `k`, Jiang proved that the maximum number of edges in an
`n`-vertex graph having no cycle with `k` distinct chords incident to one
cycle vertex is

`(k + 1) * n - (k + 1) ^ 2`

as soon as `3 * k + 3 ≤ n`.

The mathematical proof and a detailed map of the formalization are in
`tex/767.tex`.

Reference: T. Jiang, *A note on a conjecture about cycles with many incident
chords*, J. Graph Theory 46 (2004), 180--182.
-/

open Finset
open SimpleGraph
open scoped SimpleGraph

namespace Erdos767

noncomputable section

universe u

open scoped Classical in
/-- A graph has the forbidden configuration for Problem 767 when a simple
cycle has at least `k` distinct chord edges which share a cycle vertex.

The embedding selects distinct opposite endpoints.  `Walk.IsChord` says that
the selected ambient edge joins two vertices of the cycle and is not a rim
edge of the cycle.  The explicit support condition on the common endpoint is
needed when `k = 0`. -/
def HasCycleWithKIncidentChords {V : Type u} (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, c.IsChord s(v, f i)

open scoped Classical in
/-- The admissibility predicate in the definition of `g_k(n)`. -/
def AvoidsCycleWithKIncidentChords {V : Type u} (k : ℕ) (G : SimpleGraph V) : Prop :=
  ¬HasCycleWithKIncidentChords k G

open scoped Classical in
/-- The extremal number from Problem 767, using labelled graphs on `Fin n`.
Every finite graph on `n` vertices is isomorphic to one of these graphs. -/
def chordCycleExtremalNumber (k n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : SimpleGraph (Fin n) =>
    AvoidsCycleWithKIncidentChords k G).sup fun G => G.edgeFinset.card

open scoped Classical in
theorem erdos_767 (k n : ℕ) (hk : 0 < k) (hn : 3 * k + 3 ≤ n) :
    chordCycleExtremalNumber k n =
      (k + 1) * n - (k + 1) ^ 2 := by
  sorry

end

end Erdos767
