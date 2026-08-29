/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureFiniteSegmentation
import ErdosProblems.Erdos599.HalfwayPostClosureSourceAbsorption
import ErdosProblems.Erdos599.HalfwayPostClosureTerminalAbsorption

/-!
# Unconditional finite post-closure contact segmentation

The moving reference difference absorbs every uncovered hole source, and
the same chronology argument absorbs every finite assigned terminal.  These
two actual boundary theorems close the last hypotheses of the exact finite
closed/classified segmentation constructor.
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

/-- The finite branch of the actual compressor assignment has a complete,
exact mixed contact segmentation, with no endpoint or safety premise. -/
theorem exists_actualFiniteClosedClassifiedContactSegmentation_with_contactSet_subset
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace) :
    ∃ D : FiniteClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace)
      Rlimit.closedSet, D.toChain.contactSet ⊆ Rlimit.closedSet := by
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
  have hv :
      (A.assignment.produced.bracket.assignment.assigned s).terminal? =
        some (S.vertex S.lastEdge) := by
    rw [hS]
    simp only [AltPath.terminal?, FiniteRunWalk.toFiniteTrace_terminal,
      S.toFiniteRunWalk_final_last]
    rfl
  have hterminal : S.vertex S.lastEdge ∈ Rlimit.closedSet :=
    A.finite_terminal_mem_closedSet s hv
  exact A.exists_finiteClosedClassifiedContactSegmentation_of_endpoints_absorbed_with_contacts
    s S hS hinitial hterminal

/-- Original existence interface, forgetting only the additional exact
closed-contact certificate. -/
theorem exists_actualFiniteClosedClassifiedContactSegmentation
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace) :
    Nonempty (FiniteClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace)
      Rlimit.closedSet) := by
  obtain ⟨D, _hcontacts⟩ :=
    A.exists_actualFiniteClosedClassifiedContactSegmentation_with_contactSet_subset s S hS
  exact ⟨D⟩

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.exists_actualFiniteClosedClassifiedContactSegmentation
