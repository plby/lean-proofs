/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureTwoWarpMatchingIncidence
import ErdosProblems.Erdos599.TwoWarpMatchingForwardOrbit

/-!
# The actual post-closure matching orbit

The source of every actual fractured-assignment route is a closed contact
where the later interval row has a forward-exclusive edge leaving the closing
set.  The generic two-warp orbit theorem can therefore be applied directly at
that internal occurrence; no ambient-source or unmatched-component premise is
needed.

The helpers below retain the exact endpoint geometry used by the finite and
infinite hammock closures.  The projected-return and stopped outcomes are not
silently discarded: they remain the two honest boundary cases which the final
source/sink assembly must handle.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating
open _root_.Erdos599.TwoWarpMatchingTraversal

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- The complete forward-orbit outcome at an actual cut source. -/
theorem exists_actualForwardOrbitOutcome
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    Nonempty (ForwardOrbitOutcome T.interval.ambientInterval
      C.ladder.limitWarp Rlimit.closedSet x) := by
  apply exists_forwardOrbitOutcome
    T.interval.ambientInterval_linkage.isWarp
    (C.legal.warpStages (Ladder.finalStage (succ kappa)))
    (M.assignmentSource_mem_closedSet hx)
  obtain ⟨y, _hyX, hxy⟩ := M.assignmentSource_exists_forwardStep_leaving hx
  exact ⟨.inr y, hxy⟩

/-- A distinct first return has the projected-root uniqueness required by
the identity-contraction and chronological-erasure compiler. -/
theorem actualFirstReturn_projectedRoot_unique
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      C.ladder.limitWarp x)
    (hinterior : ∀ i : Fin (P.lastIndex + 1),
      0 < i.1 → i.1 < P.lastIndex →
        P.projectedVertex i ∉ Rlimit.closedSet)
    (hterminal : P.projectedVertex
      ⟨P.lastIndex, Nat.lt_succ_self _⟩ ≠ x) :
    ∀ i, P.projectedVertex i = P.projectedVertex 0 → i.1 = 0 := by
  exact P.projectedRoot_unique_of_first_return
    (M.assignmentSource_mem_closedSet hx) hinterior hterminal

/-- The two endpoints of a distinct first return satisfy the actual finite
hammock eligibility condition. -/
theorem actualFirstReturn_hammockEligible
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (P : FinitePortPrefix T.interval.ambientInterval
      C.ladder.limitWarp x)
    (hterminal : P.projectedVertex
      ⟨P.lastIndex, Nat.lt_succ_self _⟩ ∈ Rlimit.closedSet) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof x
        (.vertex (P.projectedVertex
          ⟨P.lastIndex, Nat.lt_succ_self _⟩)) := by
  exact M.assignmentSource_hammockEligible_vertex hx hterminal

/-- An infinite no-return orbit has the actual infinite-end eligibility
condition. -/
theorem actualInfiniteOrbit_hammockEligible
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources)
    (_P : InfinitePortPrefix T.interval.ambientInterval
      C.ladder.limitWarp x) :
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof x .infinity :=
  M.assignmentSource_hammockEligible_infinity hx

#print axioms exists_actualForwardOrbitOutcome
#print axioms actualFirstReturn_projectedRoot_unique
#print axioms actualFirstReturn_hammockEligible
#print axioms actualInfiniteOrbit_hammockEligible

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
