/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteRunWalkOccurrenceOrder

/-!
# Literal forward subsegments of a concrete compressor input

Unlike an abstract `FiniteRunWalk`, a `RunCompressor.FiniteInput` remembers
the directed edge at every numeric traversal coordinate.  Hence an interval
whose colours are forward has a canonical literal directed path.  This is
the construction used for contact pieces; it does not infer path order from
the weaker support-only `ProjectedRun` interface.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.FiniteInput

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

/-- The canonical forward directed path through coordinates `a,...,b`. -/
noncomputable def forwardSegment (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (hforward : ∀ k : Fin S.lastEdge, a ≤ k.1 → k.1 < b →
      S.colour k = .forward) :
    FinitePath D := by
  let hinj : ∀ {i j}, i ≤ a + (b - a) → j ≤ a + (b - a) →
      S.vertex i = S.vertex j → i = j := by
    intro i j hi hj hij
    apply S.vertex_injective_on (by omega) (by omega) hij
  exact forwardIntervalPath S.vertex a (b - a) hinj (by
    intro k hk
    let j : Fin S.lastEdge := ⟨a + k, by omega⟩
    have hjle : a ≤ j.1 := by
      change a ≤ a + k
      omega
    have hjlt : j.1 < b := by
      change a + k < b
      omega
    simpa only [j] using S.forward_adj j
      (hforward j hjle hjlt))

@[simp] theorem forwardSegment_start (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) (hforward) :
    (S.forwardSegment a b hab hb hforward).start = S.vertex a := by
  simp [forwardSegment, forwardIntervalPath]

@[simp] theorem forwardSegment_finish (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) (hforward) :
    (S.forwardSegment a b hab hb hforward).finish = S.vertex b := by
  simp [forwardSegment, forwardIntervalPath, Nat.add_sub_of_le hab.le]

theorem forwardSegment_support (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) (hforward) :
    (S.forwardSegment a b hab hb hforward).support =
      S.vertex '' Set.Icc a b := by
  simp only [forwardSegment]
  rw [forwardIntervalPath_support]
  congr 2
  omega

theorem forwardSegment_edgeSet (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge) (hforward) :
    (S.forwardSegment a b hab hb hforward).edgeSet =
      {e | ∃ k, a ≤ k ∧ k < b ∧
        e = (S.vertex k, S.vertex (k + 1))} := by
  simp only [forwardSegment]
  rw [forwardIntervalPath_edgeSet_eq]
  ext e
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨a + k, Nat.le_add_right _ _, by omega, rfl⟩
  · rintro ⟨k, hak, hkb, rfl⟩
    refine ⟨k - a, by omega, ?_⟩
    rw [Nat.add_sub_of_le hak]

/-- Every raw coordinate in one maximal run has the run's direction. -/
theorem colour_eq_runDirection (S : FiniteInput D)
    (i : Fin S.runs.length) {k : Nat}
    (hlo : runLower S.runs i.1 ≤ k)
    (hhi : k < runLower S.runs (i.1 + 1)) :
    S.colour ⟨k, by
      rw [runLower_succ S.runs i.2] at hhi
      exact hhi.trans_le (S.runUpper_le_lastEdge i)⟩ = S.runDirection i := by
  have hoff : k - runLower S.runs i.1 < (S.runs.get i).length := by
    have hsucc : runLower S.runs (i.1 + 1) =
        runLower S.runs i.1 + (S.runs.get i).length := by
      simpa using runLower_succ S.runs i.2
    rw [hsucc] at hhi
    omega
  have h := S.colour_run_offset i hoff
  have heq : runLower S.runs i.1 +
      (k - runLower S.runs i.1) = k := Nat.add_sub_of_le hlo
  simpa only [heq] using h

end Erdos599.Alternating.RunCompressor.FiniteInput

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.forwardSegment_edgeSet
#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.colour_eq_runDirection
