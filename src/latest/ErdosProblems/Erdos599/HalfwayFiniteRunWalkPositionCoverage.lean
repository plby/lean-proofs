/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteRunWalkContactEnumeration

/-!
# Every finite traversal coordinate lies in a compressed run

Consecutive run intervals cover the full integer interval from zero through
the final position.  Choosing the first run whose end is at least a given
coordinate produces the required occurrence; minimality puts the coordinate
after that run's beginning.
-/

noncomputable section

open Set

namespace Erdos599.Alternating

universe u

variable {V : Type u} {D : Digraph V}

namespace FiniteRunWalk

noncomputable def coveringRuns (W : FiniteRunWalk D) (n : Nat) :
    Finset (Fin (W.lastIndex + 1)) := by
  classical
  exact Finset.univ.filter fun i => n ≤ (W.run i).last

theorem coveringRuns_nonempty (W : FiniteRunWalk D) (n : Nat)
    (hn : n ≤ W.finalPosition) : (W.coveringRuns n).Nonempty := by
  refine ⟨W.lastRunIndex, ?_⟩
  classical
  simpa [coveringRuns, finalPosition]

noncomputable def firstCoveringRun (W : FiniteRunWalk D) (n : Nat)
    (hn : n ≤ W.finalPosition) : Fin (W.lastIndex + 1) :=
  (W.coveringRuns n).min' (W.coveringRuns_nonempty n hn)

theorem firstCoveringRun_covers (W : FiniteRunWalk D) (n : Nat)
    (hn : n ≤ W.finalPosition) :
    n ≤ (W.run (W.firstCoveringRun n hn)).last := by
  have hmem := Finset.min'_mem (W.coveringRuns n)
    (W.coveringRuns_nonempty n hn)
  classical
  simp only [coveringRuns, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem
  change n ≤ (W.run (W.firstCoveringRun n hn)).last at hmem
  exact hmem

theorem firstCoveringRun_first_le (W : FiniteRunWalk D) (n : Nat)
    (hn : n ≤ W.finalPosition) :
    (W.run (W.firstCoveringRun n hn)).first ≤ n := by
  let i := W.firstCoveringRun n hn
  change (W.run i).first ≤ n
  by_cases hi0 : i.1 = 0
  · have hieq : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext hi0
    rw [hieq, W.starts_zero]
    exact Nat.zero_le n
  · let p : Fin (W.lastIndex + 1) := ⟨i.1 - 1, by omega⟩
    have hpi : p < i := by
      change i.1 - 1 < i.1
      omega
    have hpnot : p ∉ W.coveringRuns n := by
      intro hp
      have hmin := Finset.min'_le (W.coveringRuns n) p hp
      change i ≤ p at hmin
      exact (not_le_of_gt hpi) hmin
    have hnprev : (W.run p).last < n := by
      classical
      simp only [coveringRuns, Finset.mem_filter, Finset.mem_univ,
        true_and] at hpnot
      omega
    let k : Fin W.lastIndex := ⟨i.1 - 1, by omega⟩
    have hkcast : k.castSucc = p := by
      apply Fin.ext
      rfl
    have hksucc : k.succ = i := by
      apply Fin.ext
      dsimp [k]
      omega
    rw [← hksucc, ← W.consecutive k, hkcast]
    exact hnprev.le

/-- Every bounded traversal coordinate gives an actual trace occurrence. -/
def occurrenceAt (W : FiniteRunWalk D) (n : Nat)
    (hn : n ≤ W.finalPosition) : W.VertexOccurrence (W.vertex n) where
  runIndex := W.firstCoveringRun n hn
  position := n
  first_le := W.firstCoveringRun_first_le n hn
  le_last := W.firstCoveringRun_covers n hn
  value_eq := rfl

theorem vertex_mem_toFiniteTrace (W : FiniteRunWalk D) (n : Nat)
    (hn : n ≤ W.finalPosition) :
    W.vertex n ∈ (AltPath.finite W.toFiniteTrace).vertexSet := by
  let O := W.occurrenceAt n hn
  simp only [AltPath.vertexSet, FiniteTrace.vertexSet, Set.mem_iUnion]
  exact ⟨O.runIndex, O.mem_run_support⟩

theorem vertexPosition_vertex (W : FiniteRunWalk D) (n : Nat)
    (hn : n ≤ W.finalPosition) :
    W.vertexPosition (W.vertex n) (W.vertex_mem_toFiniteTrace n hn) = n :=
  W.vertexPosition_eq_occurrence (W.vertex_mem_toFiniteTrace n hn)
    (W.occurrenceAt n hn)

/-- A break coordinate lying in `X` is carried by a concrete forward run. -/
theorem breakPosition_run_direction_forward
    (W : FiniteRunWalk D) (X : Set V)
    (hbackwardOff : ∀ l ∈ (AltPath.finite W.toFiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support X)
    (i : Fin (W.breakCount X + 1))
    (hiX : W.breakPoint X i ∈ X) :
    (W.run (W.occurrenceAt (W.breakPosition X i)
      (W.breakPosition_le_final X i)).runIndex).link.direction = .forward := by
  exact (W.occurrenceAt (W.breakPosition X i)
    (W.breakPosition_le_final X i)).direction_eq_forward_of_mem W
      hbackwardOff hiX

end FiniteRunWalk
end Erdos599.Alternating

#print axioms Erdos599.Alternating.FiniteRunWalk.firstCoveringRun_first_le
#print axioms Erdos599.Alternating.FiniteRunWalk.vertex_mem_toFiniteTrace
#print axioms Erdos599.Alternating.FiniteRunWalk.breakPosition_run_direction_forward
