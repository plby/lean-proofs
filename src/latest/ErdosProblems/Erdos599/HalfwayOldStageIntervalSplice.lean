/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOldStageIntervalTransaction
import ErdosProblems.Erdos599.HalfwayScheduledSafePathTransaction
import ErdosProblems.Erdos599.DeferredLadderRoofTransport
import ErdosProblems.Erdos599.GroundingSuccessorRoofTransport
import ErdosProblems.Erdos599.SliceSpliceSource

/-!
# Splicing the old essential reference through the 9.31 interval

The old-to-new transaction is a linkage whose left boundary is the complete
old ladder frontier.  It must therefore be attached to the *essential old
reference*, not to the raw accumulated warp: the latter also contains
inessential marker components and has the wrong boundary.

This file constructs that source-faithful row.  Its left endpoint set is the
literal initial set of the old essential reference.  This is deliberately not
identified with the ambient source, since marker-starting reference members
are genuine constituents of the ladder construction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Ladder
open CardinalInduction
open CardinalInduction.SliceSpliceSource

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-! ## A source-free tight-linkage constructor

The usual structural constructor assumes that the left endpoint set is a
subset of the ambient web source.  The old ladder reference can additionally
start at ladder markers.  Warp disjointness itself gives the exact endpoint
purity when the left endpoint set is the family's own initial set.
-/

/-- A finite warp is a tight linkage between its own initial and terminal
frontiers.  No ambient-source hypothesis is needed. -/
theorem tightLinkageBetween_initialSet_of_structural
    {R : Set V} {W : Set Gamma.DPath}
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (hterminal : Gamma.terminalFrontier W ⊆ R)
    (hright : MeetsOnlyAtTerminal Gamma W R) :
    TightLinkageBetween Gamma (Gamma.initialSet W) R W := by
  refine ⟨⟨hW, hfinite, rfl, hterminal, ?_⟩, hright⟩
  intro p hp
  obtain ⟨f, rfl⟩ := hfinite hp
  have hinitial : f.support ∩ Gamma.initialSet W = {f.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, q, hqW, hqx⟩
      have hxq : x ∈ q.support := hqx ▸ q.initial_mem_support
      have hpq : (Sum.inl f : Gamma.DPath) = q := by
        by_contra hpq
        exact Set.disjoint_left.1 (hW hp hqW hpq) hxf hxq
      subst q
      exact Set.mem_singleton_iff.2 hqx.symm
    · intro x hx
      have hxeq : x = f.start := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.start_mem_support, Sum.inl f, hp, rfl⟩
  have htarget : f.support ∩ R = {f.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxR⟩
      exact Set.mem_singleton_iff.2
        (Option.some.inj (hright (Sum.inl f) hp x hxf hxR)).symm
    · intro x hx
      have hxeq : x = f.finish := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.finish_mem_support,
        hterminal ⟨Sum.inl f, hp, rfl⟩⟩
  refine ⟨f, rfl, ?_, hinitial⟩
  rw [Set.inter_union_distrib_left, hinitial, htarget]
  simp only [Set.singleton_union]

/-- A finite warp is a tight linkage between its own initial and terminal
frontiers.  No ambient-source hypothesis is needed. -/
theorem tightLinkageBetween_initialSet_terminalFrontier
    {W : Set Gamma.DPath}
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W) :
    TightLinkageBetween Gamma (Gamma.initialSet W)
      (Gamma.terminalFrontier W) W := by
  have hright : MeetsOnlyAtTerminal Gamma W
      (Gamma.terminalFrontier W) := by
    intro p hp x hxp hxterminal
    obtain ⟨f, rfl⟩ := hfinite hp
    have hx : x ∈ ({f.finish} : Set V) :=
      DWeb.IsWarp.finite_support_inter_terminalFrontier Gamma hW hp
        ⟨hxp, hxterminal⟩
    exact congrArg some (Set.mem_singleton_iff.1 hx).symm
  refine ⟨⟨hW, hfinite, rfl, Set.Subset.rfl, ?_⟩, hright⟩
  intro p hp
  obtain ⟨f, rfl⟩ := hfinite hp
  have hinitial : f.support ∩ Gamma.initialSet W = {f.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, q, hqW, hqx⟩
      have hxq : x ∈ q.support := hqx ▸ q.initial_mem_support
      have hpq : (Sum.inl f : Gamma.DPath) = q := by
        by_contra hpq
        exact Set.disjoint_left.1 (hW hp hqW hpq) hxf hxq
      subst q
      exact Set.mem_singleton_iff.2 hqx.symm
    · intro x hx
      have hxeq : x = f.start := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.start_mem_support, Sum.inl f, hp, rfl⟩
  have hterminal : f.support ∩ Gamma.terminalFrontier W =
      {f.finish} := by
    apply Set.Subset.antisymm
    · exact DWeb.IsWarp.finite_support_inter_terminalFrontier Gamma hW hp
    · intro x hx
      have hxeq : x = f.finish := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.finish_mem_support, Sum.inl f, hp, rfl⟩
  refine ⟨f, rfl, ?_, hinitial⟩
  rw [Set.inter_union_distrib_left, hinitial, hterminal]
  simp only [Set.singleton_union]

namespace OldStageIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {z : V}

/-- The old essential reference which is to be advanced by this interval. -/
def oldReference (_T : OldStageIntervalTransaction C z) : Set Gamma.DPath :=
  ladderReference C.ladder C.oldStage

/-- The old essential reference is a tight linkage to the old slice, with
its exact (possibly marker-containing) initial boundary. -/
theorem oldReference_tight (T : OldStageIntervalTransaction C z) :
    TightLinkageBetween Gamma (Gamma.initialSet T.oldReference)
      C.oldSlice T.oldReference := by
  have h := tightLinkageBetween_initialSet_terminalFrontier
    (ladderReference.isWarp C.legal)
    (ladderReference.finiteCharacter (Gamma := Gamma)
      (L := C.ladder) (a := C.oldStage))
  simpa only [oldReference,
    ladderReference.terminalFrontier_eq C.legal] using h

/-- Every old reference vertex lies below the old frontier. -/
theorem oldReference_vertexSet_subset_roof
    (T : OldStageIntervalTransaction C z) :
    Gamma.vertexSet T.oldReference ⊆ Gamma.roof C.oldSlice := by
  exact ladderReference.vertexSet_subset_roof C.legal
    (DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier
      C.legal C.oldStage)

/-- The old reference cannot meet the later frontier before its own
terminal. -/
theorem oldReference_meetsOnlyAtNew
    (T : OldStageIntervalTransaction C z) :
    MeetsOnlyAtTerminal Gamma T.oldReference C.newSlice := by
  exact meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
    (C.legal.frontiersEssential C.oldStage)
    T.oldReference_vertexSet_subset_roof T.oldReference_tight.2
    (C.legal.strictFrontierChronology C.old_lt_new)

/-- A lifted interval member and an old essential reference member can meet
only at their common splice vertex. -/
theorem oldReference_starCompatible
    (T : OldStageIntervalTransaction C z) :
    Gamma.StarCompatible T.oldReference T.ambientInterval := by
  intro p hp q hq x hxp hxq
  have hqAmbient : q ∈ T.ambientInterval := hq
  rw [T.ambientInterval_eq_lift] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  have hxOldRaw : x ∈ Gamma.vertexSet (C.ladder.warpAt C.oldStage) := by
    exact ⟨p, hp.1, hxp⟩
  have hxRawRoof : x ∈ Gamma.roof
      (Gamma.terminalFrontier (C.ladder.warpAt C.oldStage)) :=
    DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier
      C.legal C.oldStage hxOldRaw
  have hxeq : x = r.initial := by
    by_contra hxne
    exact (C.ladder.liftStagePath_not_mem_roof_of_ne_initial
      C.oldStage r hxq hxne) hxRawRoof
  have hxOldSlice : x ∈ C.oldSlice := by
    rw [← T.ambientInterval_linkage.initialSet_eq]
    exact ⟨C.ladder.liftStagePath C.oldStage r, hqAmbient,
      (C.ladder.initial_liftStagePath C.oldStage r).trans hxeq.symm⟩
  have hpterminal : Gamma.terminal? p = some x :=
    T.oldReference_tight.2 p hp x hxp hxOldSlice
  exact ⟨hpterminal,
    (C.ladder.initial_liftStagePath C.oldStage r).trans hxeq.symm⟩

/-- The concrete old-reference ⊕ interval family. -/
def splicedIntervalRow (T : OldStageIntervalTransaction C z) :
    Set Gamma.DPath :=
  Gamma.star T.oldReference_starCompatible

/-- The spliced row is a tight linkage from the exact initial boundary of
the old essential reference to the new slice. -/
theorem splicedIntervalRow_tight
    (T : OldStageIntervalTransaction C z) :
    TightLinkageBetween Gamma (Gamma.initialSet T.oldReference)
      C.newSlice T.splicedIntervalRow := by
  let hcompat := T.oldReference_starCompatible
  have hcover : Gamma.terminalFrontier T.oldReference ⊆
      Gamma.initialSet T.ambientInterval := by
    rw [T.ambientInterval_linkage.initialSet_eq, oldReference,
      ladderReference.terminalFrontier_eq C.legal]
  change TightLinkageBetween Gamma (Gamma.initialSet T.oldReference)
    C.newSlice (Gamma.star hcompat)
  rw [← initialSet_star_eq hcompat]
  apply tightLinkageBetween_initialSet_of_structural
  · exact Gamma.isWarp_star T.oldReference_tight.1.isWarp
      T.ambientInterval_linkage.isWarp hcompat
  · exact hasFiniteCharacter_star
      T.oldReference_tight.1.finiteCharacter
      T.ambientInterval_linkage.finiteCharacter hcompat
  · exact (terminalFrontier_star_subset
      T.oldReference_tight.1.finiteCharacter hcompat hcover).trans
      T.ambientInterval_linkage.terminalFrontier_subset
  · exact meetsOnlyAtTerminal_star
      T.oldReference_tight.1.finiteCharacter
      T.oldReference_meetsOnlyAtNew
      T.ambientInterval_meetsOnlyAtTerminal hcompat hcover

/-- The spliced row retains exactly the old essential reference's initial
boundary, including any marker-starting members. -/
theorem initialSet_splicedIntervalRow
    (T : OldStageIntervalTransaction C z) :
    Gamma.initialSet T.splicedIntervalRow =
      Gamma.initialSet T.oldReference := by
  exact initialSet_star_eq T.oldReference_starCompatible

/-- Every interval member begins at an old-reference terminal. -/
theorem ambientInterval_initial_mem_oldReference_terminal
    (T : OldStageIntervalTransaction C z) {q : Gamma.DPath}
    (hq : q ∈ T.ambientInterval) :
    q.initial ∈ Gamma.terminalFrontier T.oldReference := by
  rw [oldReference, ladderReference.terminalFrontier_eq C.legal]
  have hi : q.initial ∈ Gamma.initialSet T.ambientInterval :=
    ⟨q, hq, rfl⟩
  rw [T.ambientInterval_linkage.initialSet_eq] at hi
  exact hi

/-- Star neither loses nor creates finite terminals relative to the concrete
ambient interval.  Thus exact terminal coverage can be transported from the
interval transaction whenever it is available. -/
theorem terminalFrontier_splicedIntervalRow
    (T : OldStageIntervalTransaction C z) :
    Gamma.terminalFrontier T.splicedIntervalRow =
      Gamma.terminalFrontier T.ambientInterval := by
  apply Set.Subset.antisymm
  · apply terminalFrontier_star_subset
      T.oldReference_tight.1.finiteCharacter
      T.oldReference_starCompatible
    intro x hx
    rw [T.ambientInterval_linkage.initialSet_eq]
    rw [oldReference, ladderReference.terminalFrontier_eq C.legal] at hx
    exact hx
  · exact Gamma.terminalFrontier_subset_star
      T.ambientInterval_linkage.isWarp
      T.oldReference_starCompatible
      (fun _q hq ↦ T.ambientInterval_initial_mem_oldReference_terminal hq)

/-- The selected first-hit front occurs literally as the suffix of one
member of the spliced row.  It is generally not itself a member, because the
row prepends the corresponding old-reference path. -/
theorem exists_splicedIntervalRow_member_append_front
    (T : OldStageIntervalTransaction C z) :
    ∃ f : FinitePath Gamma.graph,
      ∃ hstart : T.front.start = f.finish,
      ∃ hinter : f.support ∩ T.front.support ⊆ {f.finish},
        (Sum.inl (f.appendFinite T.front hstart hinter) : Gamma.DPath) ∈
          T.splicedIntervalRow := by
  have hzTerminal : z ∈ Gamma.terminalFrontier T.oldReference := by
    rw [oldReference, ladderReference.terminalFrontier_eq C.legal]
    exact T.source_mem
  obtain ⟨p, hpOld, hpz⟩ := hzTerminal
  obtain ⟨f, rfl⟩ := T.oldReference_tight.1.finiteCharacter hpOld
  have hfinish : f.finish = z := Option.some.inj hpz
  have hstart : T.front.start = f.finish :=
    T.front_start.trans hfinish.symm
  have hinter : f.support ∩ T.front.support ⊆ {f.finish} := by
    intro x hx
    have hcontact := T.oldReference_starCompatible
      (Sum.inl f) hpOld (Sum.inl T.front) T.front_mem_interval
      x hx.1 hx.2
    exact Set.mem_singleton_iff.2
      (Option.some.inj hcontact.1).symm
  refine ⟨f, hstart, hinter, ?_⟩
  let old : T.oldReference := ⟨Sum.inl f, hpOld⟩
  refine ⟨old, ?_⟩
  dsimp only [splicedIntervalRow, old]
  simp only [DWeb.starPath]
  split
  next h =>
    let q := Classical.choose h
    have hqInterval : q ∈ T.ambientInterval :=
      (Classical.choose_spec h).1
    have hqstart : q.initial = f.finish :=
      (Classical.choose_spec h).2
    have hqeq : q = (Sum.inl T.front : Gamma.DPath) := by
      apply DWeb.IsWarp.eq_of_initial_eq Gamma
        T.ambientInterval_linkage.isWarp hqInterval T.front_mem_interval
      exact hqstart.trans hstart.symm
    dsimp only [q] at hqeq ⊢
    simp only [hqeq]
    change (Sum.inl (f.appendFinite T.front _ _) : Gamma.DPath) =
      Sum.inl (f.appendFinite T.front hstart hinter)
    rfl
  next h =>
    exfalso
    apply h
    exact ⟨Sum.inl T.front, T.front_mem_interval, hstart⟩

/-- Every selected-front vertex survives in the source-faithful row. -/
theorem front_support_subset_splicedIntervalRow
    (T : OldStageIntervalTransaction C z) :
    T.front.support ⊆ Gamma.vertexSet T.splicedIntervalRow := by
  intro x hx
  exact Gamma.mem_vertexSet_star_of_mem_new
    T.ambientInterval_linkage.isWarp T.oldReference_starCompatible
    (fun _q hq ↦ T.ambientInterval_initial_mem_oldReference_terminal hq)
    T.front_mem_interval hx

/-- Every directed edge of the selected first-hit front is a real row edge. -/
theorem front_edgeSet_subset_splicedIntervalRow
    (T : OldStageIntervalTransaction C z) :
    T.front.edgeSet ⊆ Alternating.familyEdges T.splicedIntervalRow := by
  obtain ⟨f, hstart, hinter, hmember⟩ :=
    T.exists_splicedIntervalRow_member_append_front
  intro e he
  simp only [Alternating.familyEdges, Set.mem_iUnion]
  refine ⟨Sum.inl (f.appendFinite T.front hstart hinter), hmember, ?_⟩
  change e ∈ (f.appendFinite T.front hstart hinter).edgeSet
  rw [FinitePath.edgeSet_appendFinite]
  exact Or.inr he

/-- The external target suffix meets the old essential reference only at
the interval splice point, if it meets it at all.  The stage-web lift leaves
the old roof immediately after its initial vertex, while every old-reference
vertex lies in that roof. -/
theorem oldReference_tail_inter_subset
    (T : OldStageIntervalTransaction C z) :
    Gamma.vertexSet T.oldReference ∩ T.tail.support ⊆
      {T.tail.start} := by
  intro x hx
  have hxOldRoof : x ∈ Gamma.roof C.oldSlice :=
    T.oldReference_vertexSet_subset_roof hx.1
  have hxPath : x ∈ T.path.support :=
    T.tail_support_subset_path hx.2
  have hpathLift := T.path_mem_safe
  rw [T.safe.ambient_eq_lift] at hpathLift
  obtain ⟨q, hq, hqeq⟩ := hpathLift
  have hxLift : x ∈
      (C.ladder.liftStagePath C.oldStage q).support := by
    rw [hqeq]
    exact hxPath
  have hxRawRoof : x ∈ Gamma.roof
      (Gamma.terminalFrontier (C.ladder.warpAt C.oldStage)) := by
    rw [← Gamma.roof_essential,
      ← C.ladder.frontier_eq_essential_terminalFrontier
        C.legal.roofsSourceAtStages C.oldStage]
    exact hxOldRoof
  have hxInitial : x = T.path.start := by
    by_contra hxne
    have hxneQ : x ≠ q.initial := by
      intro hxeq
      apply hxne
      calc
        x = q.initial := hxeq
        _ = (C.ladder.liftStagePath C.oldStage q).initial :=
          (C.ladder.initial_liftStagePath C.oldStage q).symm
        _ = T.path.start := congrArg DirectedPath.Path.initial hqeq
    exact (C.ladder.liftStagePath_not_mem_roof_of_ne_initial
      C.oldStage q hxLift hxneQ) hxRawRoof
  have hxFront : x ∈ T.front.support := by
    have hpathFrontInitial : T.path.start = T.front.start :=
      T.path_start.trans T.front_start.symm
    rw [hxInitial, hpathFrontInitial]
    exact T.front.start_mem_support
  have hxInter : x ∈ T.front.support ∩ T.tail.support :=
    ⟨hxFront, hx.2⟩
  rw [T.front_tail_inter] at hxInter
  simpa only [T.tail_start] using hxInter

/-- The complete source-faithful row and the retained target suffix have
exactly the intended single splice contact. -/
theorem splicedIntervalRow_tail_inter
    (T : OldStageIntervalTransaction C z) :
    Gamma.vertexSet T.splicedIntervalRow ∩ T.tail.support =
      {T.tail.start} := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases CardinalInduction.SliceSpliceSource.vertexSet_star_subset_union
      T.oldReference_starCompatible hx.1 with hxOld | hxInterval
    · exact T.oldReference_tail_inter_subset ⟨hxOld, hx.2⟩
    · have hxContact : x ∈
          Gamma.vertexSet T.ambientInterval ∩ T.tail.support :=
        ⟨hxInterval, hx.2⟩
      rw [T.interval_tail_inter] at hxContact
      simpa only [T.tail_start] using hxContact
  · intro x hx
    have hxeq : x = T.tail.start := Set.mem_singleton_iff.1 hx
    subst x
    refine ⟨?_, T.tail.start_mem_support⟩
    apply T.front_support_subset_splicedIntervalRow
    rw [T.tail_start]
    exact T.front.finish_mem_support

end OldStageIntervalTransaction

#print axioms tightLinkageBetween_initialSet_terminalFrontier
#print axioms OldStageIntervalTransaction.oldReference_starCompatible
#print axioms OldStageIntervalTransaction.exists_splicedIntervalRow_member_append_front
#print axioms OldStageIntervalTransaction.splicedIntervalRow_tail_inter

end LinkageBlueprint
end Blueprint
end Erdos599
