/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteInputBreakInterval
import ErdosProblems.Erdos599.HalfwayFiniteInputDirectionEdgeCoverage

/-!
# Directed provenance of consecutive contact intervals
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.FiniteInput

universe u

variable {V : Type u} {D : Digraph V}

theorem breakIntervalPath_directionEdges_subset
    (S : FiniteInput D) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X)) (d : Direction) :
    (S.breakIntervalPath X i).directionEdges d ⊆
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).directionEdges d := by
  exact S.coordinateInterval_directionEdges_subset _ _ _ _ d

end Erdos599.Alternating.RunCompressor.FiniteInput

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.breakIntervalPath_directionEdges_subset
