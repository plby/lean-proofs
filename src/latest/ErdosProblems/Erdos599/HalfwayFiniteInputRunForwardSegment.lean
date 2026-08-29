/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteInputForwardSegment

/-!
# Forward coordinate segments inside a concrete compressed run

For the actual compressor, a forward maximal run is literally the directed
coordinate interval.  Every nonempty subinterval therefore gives a
directed finite subpath of that run, with exact endpoints and edges.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.FiniteInput

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

noncomputable def runForwardSegment (S : FiniteInput D)
    (i : Fin S.runs.length) (a b : Nat)
    (ha : runLower S.runs i.1 ≤ a)
    (hb : b ≤ runLower S.runs (i.1 + 1))
    (hab : a < b)
    (hdir : (S.projectedRun i).link.direction = .forward) :
    FinitePath D := by
  have hbLast : b ≤ S.lastEdge := by
    rw [runLower_succ S.runs i.2] at hb
    exact hb.trans (S.runUpper_le_lastEdge i)
  have hrun : S.runDirection i = .forward :=
    (S.projectedRun_direction i).symm.trans hdir
  exact S.forwardSegment a b hab hbLast (by
    intro k hka hkb
    exact (S.colour_eq_runDirection i
      (ha.trans hka) (hkb.trans_le hb)).trans hrun)

@[simp] theorem runForwardSegment_start (S : FiniteInput D)
    (i : Fin S.runs.length) (a b : Nat) (ha hb hab hdir) :
    (S.runForwardSegment i a b ha hb hab hdir).start = S.vertex a := by
  simp [runForwardSegment]

@[simp] theorem runForwardSegment_finish (S : FiniteInput D)
    (i : Fin S.runs.length) (a b : Nat) (ha hb hab hdir) :
    (S.runForwardSegment i a b ha hb hab hdir).finish = S.vertex b := by
  simp [runForwardSegment]

theorem runForwardSegment_support (S : FiniteInput D)
    (i : Fin S.runs.length) (a b : Nat) (ha hb hab hdir) :
    (S.runForwardSegment i a b ha hb hab hdir).support =
      S.vertex '' Set.Icc a b := by
  simp only [runForwardSegment]
  exact S.forwardSegment_support a b _ _ _

theorem runForwardSegment_edgeSet (S : FiniteInput D)
    (i : Fin S.runs.length) (a b : Nat) (ha hb hab hdir) :
    (S.runForwardSegment i a b ha hb hab hdir).edgeSet =
      {e | ∃ k, a ≤ k ∧ k < b ∧
        e = (S.vertex k, S.vertex (k + 1))} := by
  simp only [runForwardSegment]
  exact S.forwardSegment_edgeSet a b _ _ _

theorem runForwardSegment_isSubpathOf (S : FiniteInput D)
    (i : Fin S.runs.length) (a b : Nat)
    (ha : runLower S.runs i.1 ≤ a)
    (hb : b ≤ runLower S.runs (i.1 + 1))
    (hab : a < b)
    (hdir : (S.projectedRun i).link.direction = .forward) :
    (S.runForwardSegment i a b ha hb hab hdir).IsSubpathOf
      (.inl (S.projectedRun i).link.path) := by
  have hrun : S.runDirection i = .forward :=
    (S.projectedRun_direction i).symm.trans hdir
  constructor
  · change (S.runForwardSegment i a b ha hb hab hdir).support ⊆
      (S.projectedRun i).link.path.support
    rw [S.runForwardSegment_support i a b ha hb hab hdir,
      S.projectedRun_support i]
    rintro x ⟨k, hk, rfl⟩
    exact ⟨k, ⟨ha.trans hk.1, hk.2.trans hb⟩, rfl⟩
  · change (S.runForwardSegment i a b ha hb hab hdir).edgeSet ⊆
      (S.projectedRun i).link.path.edgeSet
    rw [S.runForwardSegment_edgeSet i a b ha hb hab hdir,
      S.projectedRun_edgeSet_eq_forward i hrun]
    rintro e ⟨k, hka, hkb, rfl⟩
    refine ⟨k - runLower S.runs i.1, ?_, ?_⟩
    · have hupper : runLower S.runs (i.1 + 1) =
          runLower S.runs i.1 + (S.runs.get i).length := by
        simpa using runLower_succ S.runs i.2
      rw [hupper] at hb
      omega
    · have heq : runLower S.runs i.1 +
          (k - runLower S.runs i.1) = k :=
        Nat.add_sub_of_le (ha.trans hka)
      simp only [heq]

end Erdos599.Alternating.RunCompressor.FiniteInput

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.runForwardSegment_isSubpathOf
