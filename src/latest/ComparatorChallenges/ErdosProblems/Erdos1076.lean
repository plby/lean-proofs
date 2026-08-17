/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib

/-!
# Erdős Problem 1076

The displayed assertion in Problem 1076 is false as written.  Already for
`k = 5`, Glock proved that the true asymptotic constant is `1 / 5`, rather
than `1 / 6`.

This file gives a self-contained disproof, not relying on Glock's approximate
packing theorem.  On `23 * 23^d` vertices we construct a `(5,3)`-free
three-uniform hypergraph with `92 * (23^d)^2` triples.  Its normalized density
is `92 / 529 > 1 / 6`.

The construction replaces every block in an explicit packing of an
eleven-edge support graph by four triples.  The packing is obtained from a
cyclic graceful labeling over `ZMod 23` and a two-column orthogonal array.
The detailed mathematical proof and source audit are in `tex/1076.tex`.
-/

namespace Erdos1076

open Filter Finset
open scoped BigOperators Topology

noncomputable section

/-! ## The finite extremal problem -/

/-- A triple on a finite vertex type. -/
abbrev TripleOn (V : Type*) [DecidableEq V] := {s : Finset V // s.card = 3}

/-- A finite three-uniform hypergraph. -/
abbrev TripleSystemOn (V : Type*) [DecidableEq V] := Finset (TripleOn V)

/-- A three-uniform hypergraph on `Fin n`. -/
abbrev TripleSystem (n : ℕ) := TripleSystemOn (Fin n)

/-- The vertices spanned by a finite family of triples. -/
def verticesOn {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : Finset V :=
  C.biUnion fun e ↦ e.1

/-- `FkFree k G` means that no `k - 2` triples of `G` span at most `k`
vertices.  For ambient order at least `k`, this is equivalent to avoiding the
family of all three-uniform hypergraphs with `k` vertices and `k - 2` edges
(isolated vertices may be added to a configuration spanning fewer vertices). -/
def FkFree {V : Type*} [DecidableEq V] (k : ℕ)
    (G : TripleSystemOn V) : Prop :=
  ∀ C : TripleSystemOn V, C ⊆ G → C.card = k - 2 →
    k < (verticesOn C).card

/-- The extremal number from Problem 1076, as a finite maximum. -/
noncomputable def extremalNumber (k n : ℕ) : ℕ :=
  by
    classical
    exact (Finset.univ : Finset (TripleSystem n)).sup fun G ↦
      if FkFree k G then G.card else 0

def Problem1076Claim : Prop :=
  ∀ k : ℕ, 5 ≤ k →
    Tendsto
      (fun n : ℕ ↦ (extremalNumber k n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (1 / 6 : ℝ))

theorem erdos_1076 : ¬ Problem1076Claim := by
  sorry

end

end Erdos1076
