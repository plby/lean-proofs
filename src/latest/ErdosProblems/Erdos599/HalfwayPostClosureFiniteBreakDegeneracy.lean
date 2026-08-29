/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalFilteredPostClosureAssignment
import ErdosProblems.Erdos599.HalfwayPostClosureActualFiniteSegmentation
import ErdosProblems.Erdos599.HalfwayPostClosureSegmentedRoof

/-!
# Degeneracy of a particular actual finite outside interval

For exposed endpoints the actual break interval is globally safe. Its
captured-roof certificate supplies the filter of the causal closure, so a
non-strong pair forces this very interval to be degenerate. Endpoint exposure
is explicit: it cannot be recovered from an arbitrary classification choice.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

theorem finite_breakInterval_capturedByStageRoof
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    (i : Fin (S.finiteWalk.breakCount Rlimit.closedSet)) :
    CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder
      (S.breakIntervalPath Rlimit.closedSet i) := by
  refine ⟨Rlimit.later.stage, ?_⟩
  have hroof := A.assigned_vertices_subset_capturedRoof s
  rw [hS] at hroof
  exact (S.breakIntervalPath_vertexSet_subset Rlimit.closedSet i).trans hroof

theorem finite_breakInterval_isDegenerate_of_not_strong
    (A : PostClosureCompressorAssignment T)
    (hfiltered : FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
      Rlimit.closedSet Rlimit.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
        (CoherentNondegenerateHammockTracker.CapturedByStageRoof C.ladder) kappa)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    (i : Fin (S.finiteWalk.breakCount Rlimit.closedSet))
    (huOff : S.finiteWalk.breakPoint Rlimit.closedSet i.castSucc ∉
      Gamma.vertexSet C.ladder.limitWarp)
    (hvOff : S.finiteWalk.breakPoint Rlimit.closedSet i.succ ∉
      Gamma.vertexSet C.ladder.limitWarp)
    (houtside : ¬(S.breakIntervalPath Rlimit.closedSet i).vertexSet ⊆
      Rlimit.closedSet)
    (hnotStrong : ¬IsStrongImaginaryEdge Gamma C.ladder.limitWarp kappa
      (S.finiteWalk.breakPoint Rlimit.closedSet i.castSucc)
      (S.finiteWalk.breakPoint Rlimit.closedSet i.succ)) :
    IsDegenerate C.ladder.limitWarp (S.breakIntervalPath Rlimit.closedSet i)
      (.vertex (S.finiteWalk.breakPoint Rlimit.closedSet i.succ)) := by
  have hsX : s.1 ∈ Rlimit.closedSet :=
    T.uncovered_initials_subset_closedSet Rlimit A.fractured s.2
  have hstart := A.assignment.produced.bracket.assignment.starts_at s
  rw [hS] at hstart
  have hinitial : S.vertex 0 ∈ Rlimit.closedSet := by
    rw [← hstart] at hsX
    have hsX' : S.toFiniteRunWalk.vertex 0 ∈ Rlimit.closedSet := by
      simpa only [AltPath.initial, FiniteRunWalk.toFiniteTrace_initial] using hsX
    change S.toFiniteRunWalk.vertex 0 ∈ Rlimit.closedSet
    exact hsX'
  have hterminalEq :
      (A.assignment.produced.bracket.assignment.assigned s).terminal? =
        some (S.vertex S.lastEdge) := by
    rw [hS]
    simp only [AltPath.terminal?, FiniteRunWalk.toFiniteTrace_terminal,
      S.toFiniteRunWalk_final_last]
    rfl
  have hterminal : S.vertex S.lastEdge ∈ Rlimit.closedSet :=
    A.finite_terminal_mem_closedSet s hterminalEq
  have hne : S.finiteWalk.breakPoint Rlimit.closedSet i.castSucc ≠
      S.finiteWalk.breakPoint Rlimit.closedSet i.succ := by
    intro heq
    have hi := S.finiteWalk.breakPoint_injective Rlimit.closedSet heq
    have hiv := congrArg Fin.val hi
    simp only [Fin.val_castSucc, Fin.val_succ] at hiv
    omega
  have hsafe : IsSafe C.ladder.limitWarp
      (S.breakIntervalPath Rlimit.closedSet i) := by
    apply (A.finite_breakInterval_internallySafe s S hS i).isSafe_of_exposedEndpoints
    · simpa only [S.breakIntervalPath_initial] using huOff
    · intro v hv
      have heq := S.breakIntervalPath_terminal Rlimit.closedSet i
      have hvEq := Option.some.inj (hv.symm.trans heq)
      simpa only [hvEq] using hvOff
  exact hfiltered.isDegenerate_of_not_strong hne
    (A.finite_breakInterval_hammockEligible s S hS hinitial hterminal i)
    hsafe (S.breakIntervalPath_initial Rlimit.closedSet i)
    (S.breakIntervalPath_terminal Rlimit.closedSet i)
    (A.finite_breakInterval_capturedByStageRoof s S hS i)
    (S.breakIntervalPath_hammockInterior_disjoint Rlimit.closedSet i)
    houtside hnotStrong

#print axioms finite_breakInterval_capturedByStageRoof
#print axioms finite_breakInterval_isDegenerate_of_not_strong

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment
