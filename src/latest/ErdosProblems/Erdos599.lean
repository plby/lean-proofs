/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMengerAssembly

/-!
# Erdős Problem 599

Aharoni and Berger's directed infinite Menger theorem implies the requested
undirected statement.  Their result is stronger: the source and target sets
need not be independent or disjoint.

The detailed mathematical reconstruction and Leanization plan are in
`tex/599.tex`.
-/

namespace Erdos599

open SimpleGraph

universe u

/-- The affirmative resolution of Erdős Problem 599 (the Erdős--Menger
conjecture): every pair of disjoint independent vertex sets in a possibly
infinite graph admits an orthogonal path packing and separator. -/
theorem erdos_599 {V : Type u} (G : SimpleGraph V) (A B : Set V)
    (hAB : Disjoint A B) (hA : G.IsIndepSet A) (hB : G.IsIndepSet B) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  apply Bridge.erdos_599_of_directed_menger
    UnroofedMengerAssembly.directedMenger
    G A B hAB hA hB

#print axioms erdos_599

end Erdos599
