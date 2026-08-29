/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteRunWalkPositionCoverage

/-!
# Forward-run occurrences of all finite break points

Interior break points lie in `X`, so backward-link avoidance puts them on a
forward run.  The initial and terminal break points use the first and last
forward-direction conclusions of the actual projection compiler.
-/

noncomputable section

open Set

namespace Erdos599.Alternating

universe u

variable {V : Type u} {D : Digraph V}

namespace FiniteRunWalk

/-- The literal first-run occurrence at coordinate zero. -/
def initialOccurrence (W : FiniteRunWalk D) :
    W.VertexOccurrence (W.vertex 0) where
  runIndex := ⟨0, Nat.zero_lt_succ _⟩
  position := 0
  first_le := by rw [W.starts_zero]
  le_last := (W.run ⟨0, Nat.zero_lt_succ _⟩).first_lt_last.le.trans' (by
    rw [W.starts_zero])
  value_eq := rfl

/-- The literal last-run occurrence at the final coordinate. -/
def terminalOccurrence (W : FiniteRunWalk D) :
    W.VertexOccurrence (W.vertex W.finalPosition) where
  runIndex := W.lastRunIndex
  position := W.finalPosition
  first_le := (W.run W.lastRunIndex).first_lt_last.le
  le_last := le_rfl
  value_eq := rfl

@[simp] theorem initialOccurrence_position (W : FiniteRunWalk D) :
    W.initialOccurrence.position = 0 := rfl

@[simp] theorem terminalOccurrence_position (W : FiniteRunWalk D) :
    W.terminalOccurrence.position = W.finalPosition := rfl

theorem initialOccurrence_direction_forward
    (W : FiniteRunWalk D)
    (hfirst : W.toFiniteTrace.firstLink.direction = .forward) :
    (W.run W.initialOccurrence.runIndex).link.direction = .forward := by
  exact hfirst

theorem terminalOccurrence_direction_forward
    (W : FiniteRunWalk D)
    (hlast : W.toFiniteTrace.lastLink.direction = .forward) :
    (W.run W.terminalOccurrence.runIndex).link.direction = .forward := by
  exact hlast

/-- Every ordered break point has a concrete containing forward run at the
same traversal coordinate. -/
theorem exists_forwardOccurrence_breakPosition
    (W : FiniteRunWalk D) (X : Set V)
    (hbackwardOff : ∀ l ∈ (AltPath.finite W.toFiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support X)
    (hfirst : W.toFiniteTrace.firstLink.direction = .forward)
    (hlast : W.toFiniteTrace.lastLink.direction = .forward)
    (i : Fin (W.breakCount X + 1)) :
    ∃ O : W.VertexOccurrence (W.breakPoint X i),
      O.position = W.breakPosition X i ∧
      (W.run O.runIndex).link.direction = .forward := by
  rcases W.breakPosition_endpoint_or_mem X i with hi0 | hifinal | hiX
  · have hpoint : W.breakPoint X i = W.vertex 0 := by
      simp [breakPoint, hi0]
    let O : W.VertexOccurrence (W.breakPoint X i) := {
      runIndex := W.initialOccurrence.runIndex
      position := 0
      first_le := W.initialOccurrence.first_le
      le_last := W.initialOccurrence.le_last
      value_eq := hpoint.symm }
    exact ⟨O, by simp [O, hi0], by
      exact W.initialOccurrence_direction_forward hfirst⟩
  · have hpoint : W.breakPoint X i = W.vertex W.finalPosition := by
      simp [breakPoint, hifinal]
    let O : W.VertexOccurrence (W.breakPoint X i) := {
      runIndex := W.terminalOccurrence.runIndex
      position := W.finalPosition
      first_le := W.terminalOccurrence.first_le
      le_last := W.terminalOccurrence.le_last
      value_eq := hpoint.symm }
    exact ⟨O, by simp [O, hifinal], by
      exact W.terminalOccurrence_direction_forward hlast⟩
  · let O := W.occurrenceAt (W.breakPosition X i)
      (W.breakPosition_le_final X i)
    exact ⟨O, rfl,
      O.direction_eq_forward_of_mem W hbackwardOff hiX⟩

end FiniteRunWalk
end Erdos599.Alternating

#print axioms Erdos599.Alternating.FiniteRunWalk.exists_forwardOccurrence_breakPosition
