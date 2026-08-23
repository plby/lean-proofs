/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 842.
https://www.erdosproblems.com/forum/thread/842

Informal authors:
- Herbert Fleischner
- Michael Stiebitz

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos842.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos842.ColoringBridge
import ErdosProblems.Erdos842.SurvivorFibres

/-!
# Erdős Problem 842

Fleischner and Stiebitz proved that a graph obtained from `n` vertex-disjoint triangles by
adding all edges of an edge-disjoint Hamiltonian cycle is three-colorable.  The formal proof uses
Petrov's parity reconstruction of their Alon--Tarsi argument: a distinguished coefficient of the
indexed graph polynomial is congruent to two modulo four and is therefore nonzero.  The
Combinatorial Nullstellensatz then supplies a proper coloring with the three values `0`, `1`, and
`2`.
-/

open SimpleGraph

namespace Erdos842

/-- **Erdős Problem 842 (Fleischner--Stiebitz).**

If `G` is the exact union of `n` vertex-disjoint triangles and an edge-disjoint Hamiltonian cycle
on their `3n` vertices, then the chromatic number of `G` is at most three.
-/
theorem erdos_842 {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (hG : IsCyclePlusTriangles G n) :
    G.chromaticNumber ≤ 3 := by
  apply hG.chromaticNumber_le_of_canonical_centralCoeff_ne_zero
  intro triangleCoord _hdisjoint
  exact SurvivorFibres.canonicalCoeff_ne_zero n triangleCoord

end Erdos842

#print axioms Erdos842.erdos_842
