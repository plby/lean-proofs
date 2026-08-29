/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureFiniteBreakGeometry
import ErdosProblems.Erdos599.HalfwayFiniteClosedClassifiedProducer

/-!
# Finite actual closed/classified contact segmentation

This is the complete finite compressor branch.  The only geometric inputs
are absorption of its two exposed endpoints into the already constructed
moving closing set; all interval safety, eligibility, exact coverage, and
global limiting-reference data are derived from the actual assignment.
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

theorem exists_finiteClosedClassifiedContactSegmentation_of_endpoints_absorbed_with_contacts
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    (hinitial : S.vertex 0 ∈ Rlimit.closedSet)
    (hterminal : S.vertex S.lastEdge ∈ Rlimit.closedSet) :
    ∃ D : FiniteClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace)
      Rlimit.closedSet, D.toChain.contactSet ⊆ Rlimit.closedSet := by
  have hpoint : ∀ i, S.finiteWalk.breakPoint Rlimit.closedSet i ∈ Rlimit.closedSet := by
    intro i
    apply S.finiteWalk.breakPoint_mem_of_endpoints_mem Rlimit.closedSet
    · exact hinitial
    · rw [S.finiteWalk_finalPosition]
      exact hterminal
  obtain ⟨D, hcount, hpoints⟩ :=
    FiniteBreakMixedPiece.exists_finiteClosedClassifiedContactSegmentation_with_points
      S Rlimit.closedSet Rlimit.hammock_closed Rlimit.reference_closed
      (fun i _ _ ↦ A.finite_breakInterval_hammockEligible s S hS hinitial hterminal i)
      (fun i _ _ ↦ A.finite_breakInterval_internallySafe s S hS i)
      (fun i _ ↦ hpoint i.castSucc) (fun i _ ↦ hpoint i.succ)
  refine ⟨D, ?_⟩
  rintro x ⟨i, rfl⟩
  change D.point i ∈ Rlimit.closedSet
  rw [hpoints i]
  exact hpoint _

/-- Signature-compatible form which forgets only the contact-set inclusion. -/
theorem exists_finiteClosedClassifiedContactSegmentation_of_endpoints_absorbed
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    (hinitial : S.vertex 0 ∈ Rlimit.closedSet)
    (hterminal : S.vertex S.lastEdge ∈ Rlimit.closedSet) :
    Nonempty (FiniteClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace)
      Rlimit.closedSet) := by
  obtain ⟨D, _hcontacts⟩ :=
    A.exists_finiteClosedClassifiedContactSegmentation_of_endpoints_absorbed_with_contacts
      s S hS hinitial hterminal
  exact ⟨D⟩

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.exists_finiteClosedClassifiedContactSegmentation_of_endpoints_absorbed
