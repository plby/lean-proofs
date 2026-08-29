/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteBreakForwardOccurrences

/-!
# Order of concrete occurrences in a finite compressed run walk

The numeric position retained by a `FiniteRunWalk` orders containing runs:
an earlier vertex cannot be carried only by a later run.  This converts the
ordered global break list into the same-run/cross-run dichotomy needed by
the literal contact splitter.
-/

noncomputable section

open Set

namespace Erdos599.Alternating

universe u

variable {V : Type u} {D : Digraph V}

namespace FiniteRunWalk

theorem VertexOccurrence.runIndex_le_of_position_lt
    {W : FiniteRunWalk D} {x y : V}
    (O : W.VertexOccurrence x) (P : W.VertexOccurrence y)
    (hpos : O.position < P.position) : O.runIndex ≤ P.runIndex := by
  by_contra hnot
  have hPO : P.runIndex < O.runIndex := lt_of_not_ge hnot
  have hordered := W.ordered P.runIndex O.runIndex hPO
  have hPle := P.le_last
  have hOfirst := O.first_le
  omega

theorem consecutiveBreak_position_lt
    (W : FiniteRunWalk D) (X : Set V) (i : Fin (W.breakCount X)) :
    W.breakPosition X i.castSucc < W.breakPosition X i.succ := by
  exact W.breakPosition_strictMono X Fin.castSucc_lt_succ

theorem consecutiveBreak_left_zero_or_mem
    (W : FiniteRunWalk D) (X : Set V) (i : Fin (W.breakCount X)) :
    W.breakPosition X i.castSucc = 0 ∨ W.breakPoint X i.castSucc ∈ X := by
  rcases W.breakPosition_endpoint_or_mem X i.castSucc with hzero | hfinal | hX
  · exact Or.inl hzero
  · have hlt := W.consecutiveBreak_position_lt X i
    have hle := W.breakPosition_le_final X i.succ
    omega
  · exact Or.inr hX

theorem consecutiveBreak_right_final_or_mem
    (W : FiniteRunWalk D) (X : Set V) (i : Fin (W.breakCount X)) :
    W.breakPosition X i.succ = W.finalPosition ∨
      W.breakPoint X i.succ ∈ X := by
  rcases W.breakPosition_endpoint_or_mem X i.succ with hzero | hfinal | hX
  · have hlt := W.consecutiveBreak_position_lt X i
    omega
  · exact Or.inl hfinal
  · exact Or.inr hX

theorem consecutiveBreak_occurrence_runIndex_le
    (W : FiniteRunWalk D) (X : Set V) (i : Fin (W.breakCount X))
    (O : W.VertexOccurrence (W.breakPoint X i.castSucc))
    (P : W.VertexOccurrence (W.breakPoint X i.succ))
    (hO : O.position = W.breakPosition X i.castSucc)
    (hP : P.position = W.breakPosition X i.succ) :
    O.runIndex ≤ P.runIndex := by
  apply O.runIndex_le_of_position_lt P
  rw [hO, hP]
  exact W.consecutiveBreak_position_lt X i

end FiniteRunWalk
end Erdos599.Alternating

#print axioms Erdos599.Alternating.FiniteRunWalk.VertexOccurrence.runIndex_le_of_position_lt
#print axioms Erdos599.Alternating.FiniteRunWalk.consecutiveBreak_occurrence_runIndex_le
