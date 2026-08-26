import Mathlib.Combinatorics.SimpleGraph.Bipartite

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Universe-compatible balanced complete bipartite graphs

This file keeps the finite graph atom used throughout the formalization out of
the triple-system layer. Both finite parts are lifted to the ambient universe,
so a copy can live in a graph whose vertex type is in that same universe.
-/

namespace Erdos593

universe u

/-- A universe-compatible finite part of cardinality `n`. -/
abbrev FiniteBipartitePart (n : ℕ) := ULift.{u} (Fin n)

/-- The balanced complete bipartite graph `K_{n,n}`, with both parts in
universe `u`. -/
abbrev completeBipartiteNN (n : ℕ) :
    _root_.SimpleGraph
      (FiniteBipartitePart.{u} n ⊕ FiniteBipartitePart.{u} n) :=
  _root_.completeBipartiteGraph
    (FiniteBipartitePart.{u} n) (FiniteBipartitePart.{u} n)

end Erdos593
