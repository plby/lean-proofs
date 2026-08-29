/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureSafeFrontTerminal

/-!
# Incidence of the external target tail

The scheduled safe path is split at the captured frontier.  Its retained
front belongs to the post-closure blueprint, while its remaining target
tail is external data.  This file records the exact separation that is
available from the stage quotient: the tail meets the old/current roof,
and hence the activated-reference seed, only at its start.

It also records the obstruction to simply inserting that tail into the
captured-roof blueprint.  Since the tail finishes in the ambient target,
carrying all its vertices in the captured roof would force its finish to
belong to the captured frontier itself.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

private theorem selected_safe_path_mem :
    (Sum.inl T.interval.path : Gamma.DPath) ∈ T.safe.ambientFamily := by
  have h := T.interval.path_mem_safe
  rw [T.interval_safe_eq] at h
  exact h

/-- The entire stored target suffix was inserted into the closure seed
before the later stage was selected. -/
theorem tail_support_subset_closedSet :
    T.interval.tail.support ⊆ Rlimit.closedSet := by
  intro x hx
  apply T.safe_vertices_closed
  exact ⟨.inl T.interval.path, selected_safe_path_mem,
    T.interval.tail_support_subset_path hx⟩

/-- Stable capture of the closure therefore roofs the entire target suffix
at the newly selected stage. -/
theorem tail_support_subset_capturedRoof :
    T.interval.tail.support ⊆
      Gamma.roof Rlimit.capturedGeometry.newSlice := by
  exact tail_support_subset_closedSet.trans
    Rlimit.capturedGeometry_closedSet_subset_newRoof

/-- In the actual source order, the ambient target endpoint is consequently
a literal member of the captured frontier.  The later stage was chosen only
after the full safe path had been seeded. -/
theorem tail_finish_mem_capturedSlice :
    T.interval.tail.finish ∈ Rlimit.capturedGeometry.newSlice := by
  apply _root_.Erdos599.CardinalInduction.SliceSpliceConstructor.target_mem_of_mem_roof
    T.interval.tail_boundary.2
  exact tail_support_subset_capturedRoof T.interval.tail.finish_mem_support

/-- Every contact of the external target tail with the current roof is its
splice vertex.  This is the post-closure counterpart of
`ClosedOldSlice930MacroTransaction.oldRoof_tail_inter_subset`; it uses only
the actual lifted-stage provenance of the preselected safe path. -/
theorem currentRoof_tail_inter_subset :
    Gamma.roof C.newSlice ∩ T.interval.tail.support ⊆
      {T.interval.tail.start} := by
  intro x hx
  have hxPath : x ∈ T.interval.path.support :=
    T.interval.tail_support_subset_path hx.2
  have hpathLift := T.interval.path_mem_safe
  rw [T.interval_safe_eq,
    SafeCurrentStageTargetPath.toCaptured_ambientFamily,
    T.safe.ambient_eq_lift] at hpathLift
  obtain ⟨q, hq, hqeq⟩ := hpathLift
  have hxLift : x ∈
      (C.ladder.liftStagePath C.newStage q).support := by
    rw [hqeq]
    exact hxPath
  have hxRawRoof : x ∈ Gamma.roof
      (Gamma.terminalFrontier (C.ladder.warpAt C.newStage)) := by
    rw [← Gamma.roof_essential,
      ← C.ladder.frontier_eq_essential_terminalFrontier
        C.legal.roofsSourceAtStages C.newStage]
    exact hx.1
  have hxInitial : x = T.interval.path.start := by
    by_contra hxne
    have hxneQ : x ≠ q.initial := by
      intro hxeq
      apply hxne
      calc
        x = q.initial := hxeq
        _ = (C.ladder.liftStagePath C.newStage q).initial :=
          (C.ladder.initial_liftStagePath C.newStage q).symm
        _ = T.interval.path.start :=
          congrArg DirectedPath.Path.initial hqeq
    exact (C.ladder.liftStagePath_not_mem_roof_of_ne_initial
      C.newStage q hxLift hxneQ) hxRawRoof
  have hxFront : x ∈ T.interval.front.support := by
    have hpathFrontInitial :
        T.interval.path.start = T.interval.front.start :=
      T.interval.path_start.trans T.interval.front_start.symm
    rw [hxInitial, hpathFrontInitial]
    exact T.interval.front.start_mem_support
  have hxInter : x ∈
      T.interval.front.support ∩ T.interval.tail.support :=
    ⟨hxFront, hx.2⟩
  rw [T.interval.front_tail_inter] at hxInter
  simpa only [← T.interval.tail_start] using hxInter

/-- Consequently the external tail meets the complete current-plus-prefix
seed only at its start. -/
theorem referencePrefixSeed_tail_inter_subset
    (current A : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hAV : A.vertexSet = current.vertexSet ∪ Gamma.vertexSet
      (activatedReferencePrefixes C current Rlimit.closedSet)) :
    A.vertexSet ∩ T.interval.tail.support ⊆
      {T.interval.tail.start} := by
  intro x hx
  apply currentRoof_tail_inter_subset
  refine ⟨?_, hx.2⟩
  exact referencePrefixSeed.blueprint_vertices_roofed hcurrent hAV hx.1

/-- Inserting the whole external tail into a blueprint roofed at the
captured frontier forces its ambient-target endpoint to lie on that
frontier.  This is the precise compatibility condition missing from the
fixed-target moving-successor interface. -/
theorem tail_finish_mem_capturedSlice_of_carried
    (U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hUroof : U.vertexSet ⊆
      Gamma.roof Rlimit.capturedGeometry.newSlice)
    (htail : T.interval.tail.support ⊆ U.vertexSet) :
    T.interval.tail.finish ∈ Rlimit.capturedGeometry.newSlice := by
  apply _root_.Erdos599.CardinalInduction.SliceSpliceConstructor.target_mem_of_mem_roof
    T.interval.tail_boundary.2
  exact hUroof (htail T.interval.tail.finish_mem_support)

#print axioms currentRoof_tail_inter_subset
#print axioms referencePrefixSeed_tail_inter_subset
#print axioms tail_support_subset_closedSet
#print axioms tail_support_subset_capturedRoof
#print axioms tail_finish_mem_capturedSlice
#print axioms tail_finish_mem_capturedSlice_of_carried

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
