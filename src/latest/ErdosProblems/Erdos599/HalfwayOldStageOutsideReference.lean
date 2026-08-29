/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930PriorIntervalClosure
import ErdosProblems.Erdos599.HalfwayOutsideMacroAssignment

/-!
# The unchanged outside reference of the old-stage interval transaction

The old-to-new interval transaction changes only the alternating components
in `exceptionalComponents`.  The joint 9.30/9.31 closure contains those
components and every selected-reference component which meets them.  Hence,
after deleting the closed set, the selected new-stage reference is literally
the old essential reference starred with the retained canonical interval row.

This is the source-faithful replacement for a false blanket containment of
the complete new-stage reference in an arbitrary completed linkage.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Ladder
open CardinalInduction CardinalInduction.SliceCandidate

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The old-frontier splice vertex lies on the realized later essential
prefix.  This is immediate from the exact append equation, but recording it
avoids any appeal to an unexported prefix field. -/
theorem stageIntervalRealization_source_mem_rightPrefix_support
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (E : StageIntervalRealization L delta beta S) (x : S) :
    x.1 ∈ (E.rightPrefix x).support := by
  let hstart : DirectedPath.Path.initial
      (Sum.inl (E.toSegmentRealization.segment x) : Gamma.DPath) =
        (E.leftPrefix x).finish := by
    change (E.toSegmentRealization.segment x).start =
      (E.leftPrefix x).finish
    exact E.toSegmentRealization.segment_start x |>.trans
      (E.left_finish x).symm
  let hinter : (E.leftPrefix x).support ∩
      DirectedPath.Path.support
        (Sum.inl (E.toSegmentRealization.segment x) : Gamma.DPath) ⊆
        {(E.leftPrefix x).finish} := by
    change (E.leftPrefix x).support ∩
      (E.toSegmentRealization.segment x).support ⊆
        {(E.leftPrefix x).finish}
    exact (E.prefix_inter x).subset
  let appended : Gamma.DPath :=
    DirectedPath.Path.appendFinite (E.leftPrefix x)
      (.inl (E.toSegmentRealization.segment x)) hstart hinter
  have happended : appended =
      (Sum.inl (E.rightPrefix x) : Gamma.DPath) := by
    simpa only [appended] using E.append_eq x
  have hxAppend : x.1 ∈ appended.support := by
    dsimp only [appended]
    rw [DirectedPath.Path.support_appendFinite]
    apply Or.inl
    rw [← E.left_finish x]
    exact (E.leftPrefix x).finish_mem_support
  rw [happended] at hxAppend
  exact hxAppend

namespace OldStageIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {z : V}

/-- Outside the exchanged components, the transaction contains the literal
canonical ladder interval at the given old-frontier vertex. -/
theorem canonical_stageSegment_mem_ambientInterval_of_not_mem_exceptional
    (T : OldStageIntervalTransaction C z)
    (x : ↑(C.oldSlice \ C.deferredOldStageExceptional))
    (hx : x.1 ∉ T.exceptionalComponents) :
    C.ladder.liftStagePath C.oldStage
        (CardinalInduction.DeferredStageInterval.StageIntervalRealization.stageSegment
          C.deferredOldStageRealization C.legal C.old_lt_new.le x) ∈
      T.ambientInterval := by
  let H := C.ladder.stageWeb C.oldStage
  let R := C.deferredOldStageRealization
  let r : H.DPath :=
    CardinalInduction.DeferredStageInterval.StageIntervalRealization.stageSegment
      R C.legal C.old_lt_new.le x
  have hrInitial : r.initial = x.1 :=
    CardinalInduction.DeferredStageInterval.StageIntervalRealization.initial_stageSegment
      R C.legal C.old_lt_new.le x
  have hrOrdinary : r ∈ C.deferredOldStageOrdinaryFamily := by
    exact ⟨x, rfl⟩
  have hxExcluded :
      x.1 ∉ (C.deferredOldStageExceptional ∪ {z}) ∪
        oldStageContactInitials C T.safe := by
    intro hbad
    exact hx (T.excludedInitials_subset_exceptional hbad)
  have hrRestricted : r ∈
      SliceSpliceSource.initialRestriction H C.deferredOldStageOrdinaryFamily
        (C.oldSlice \ ((C.deferredOldStageExceptional ∪ {z}) ∪
          oldStageContactInitials C T.safe)) := by
    refine ⟨hrOrdinary, ?_⟩
    rw [hrInitial]
    exact ⟨x.2.1, hxExcluded⟩
  have hrRetained : r ∈ T.ordinaryRetained := by
    rw [T.ordinaryRetained_eq]
    refine ⟨hrRestricted, ?_⟩
    rw [hrInitial]
    exact hx
  have hrInterval : r ∈ T.stageInterval :=
    T.ordinaryRetained_subset hrRetained
  rw [T.ambientInterval_eq_lift]
  exact ⟨r, hrInterval, rfl⟩

/-- Every unchanged canonical essential extension is literally a member of
the source-star row. -/
theorem canonical_right_mem_splicedIntervalRow_of_not_mem_exceptional
    (T : OldStageIntervalTransaction C z)
    (x : ↑(C.oldSlice \ C.deferredOldStageExceptional))
    (hx : x.1 ∉ T.exceptionalComponents) :
    (Sum.inl
        ((C.deferredOldStageRealization)
          |>.rightPrefix x) : Gamma.DPath) ∈
      T.splicedIntervalRow := by
  let R := C.deferredOldStageRealization
  let segment := R.toSegmentRealization.segment x
  let q : Gamma.DPath := Sum.inl segment
  have hqInterval : q ∈ T.ambientInterval := by
    have h := T.canonical_stageSegment_mem_ambientInterval_of_not_mem_exceptional
      x hx
    change Sum.inl segment ∈ T.ambientInterval
    rw [← CardinalInduction.DeferredStageInterval.StageIntervalRealization.liftStagePath_stageSegment
      R C.legal C.old_lt_new.le x]
    exact h
  have hleft : (Sum.inl (R.leftPrefix x) : Gamma.DPath) ∈
      T.oldReference := by
    exact R.left_mem x
  have hqStart : q.initial = (R.leftPrefix x).finish := by
    exact (R.toSegmentRealization.segment_start x).trans
      (R.left_finish x).symm
  let old : T.oldReference :=
    ⟨(Sum.inl (R.leftPrefix x) : Gamma.DPath), hleft⟩
  refine ⟨old, ?_⟩
  dsimp only [splicedIntervalRow, old]
  simp only [DWeb.starPath]
  split
  next hmatch =>
    let q' := Classical.choose hmatch
    have hq'Mem : q' ∈ T.ambientInterval :=
      (Classical.choose_spec hmatch).1
    have hq'Start : q'.initial = (R.leftPrefix x).finish :=
      (Classical.choose_spec hmatch).2
    have hq'eq : q' = q := by
      apply DWeb.IsWarp.eq_of_initial_eq Gamma
        T.ambientInterval_linkage.isWarp hq'Mem hqInterval
      exact hq'Start.trans hqStart.symm
    rcases hqshape : q' with qf | qr
    · have hqfin : qf = segment := by
        apply Sum.inl.inj
        calc
          (Sum.inl qf : Gamma.DPath) = q' := hqshape.symm
          _ = q := hq'eq
          _ = Sum.inl segment := rfl
      subst qf
      simpa only [q', hqshape, q, segment] using R.append_eq x
    · have : (Sum.inr qr : Gamma.DPath) = Sum.inl segment := by
        calc
          (Sum.inr qr : Gamma.DPath) = q' := hqshape.symm
          _ = q := hq'eq
          _ = Sum.inl segment := rfl
      cases this
  next hmatch =>
    exfalso
    exact hmatch ⟨q, hqInterval, hqStart⟩

end OldStageIntervalTransaction

namespace ClosedPrior930IntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u z : V} {R : PriorContact930Request C W u}
variable {T : OldStageIntervalTransaction C z}

/-- All interval components changed by the bounded exchange lie in the
joint closed carrier. -/
theorem exceptionalComponents_subset_closedSet
    (Q : ClosedPrior930IntervalTransaction R T) :
    T.exceptionalComponents ⊆ Q.closedSet :=
  (R.exceptionalComponents_subset_intervalSeed T).trans Q.seed_subset

/-- Every marker-starting selected-reference component is swallowed before
the outside-reference assignment is formed. -/
theorem markerStarting_vertexSet_subset_closedSet
    (Q : ClosedPrior930IntervalTransaction R T) :
    Gamma.vertexSet
        (ladderReference.markerStarting
          (Gamma := Gamma) (L := C.ladder) (a := C.newStage)) ⊆
      Q.closedSet := by
  exact (continuation930ContactSeed.markerVertices_subset C W).trans
    ((R.contactSeed_subset).trans
      ((R.seed_subset_intervalSeed T).trans Q.seed_subset))

/-- A selected-reference member which survives the joint closed carrier is
one of the canonical essential extensions of a nonexceptional old-frontier
component. -/
theorem outside_selectedReference_eq_canonical_right
    (Q : ClosedPrior930IntervalTransaction R T)
    {p : Gamma.DPath} (hp : p ∈ outsideReference C.selectedReference Q.closedSet) :
    ∃ x : ↑(C.oldSlice \ C.deferredOldStageExceptional),
      x.1 ∉ T.exceptionalComponents ∧
      p = Sum.inl
        ((C.deferredOldStageRealization)
          |>.rightPrefix x) := by
  have hpSelected : p ∈ C.selectedReference := hp.1
  have hpSource : p.initial ∈ Gamma.source := by
    by_contra hpNotSource
    have hpMarker : p ∈ ladderReference.markerStarting
        (Gamma := Gamma) (L := C.ladder) (a := C.newStage) :=
      ⟨hpSelected, hpNotSource⟩
    have hinitialClosed : p.initial ∈ Q.closedSet :=
      Q.markerStarting_vertexSet_subset_closedSet
        ⟨p, hpMarker, p.initial_mem_support⟩
    exact Set.disjoint_left.1 hp.2 p.initial_mem_support hinitialClosed
  obtain ⟨f, rfl⟩ := ladderReference.finiteCharacter hpSelected
  have hfinishNew : f.finish ∈ C.newSlice := by
    rw [← ClubStageGeometry.terminalFrontier_selectedReference C]
    exact ⟨Sum.inl f, hpSelected, rfl⟩
  have hmeetOld : (f.support ∩ C.oldSlice).Nonempty := by
    by_cases hfinishOld : f.finish ∈ C.oldSlice
    · exact ⟨f.finish, f.finish_mem_support, hfinishOld⟩
    · have hfinishNotRoof : f.finish ∉ Gamma.roof C.oldSlice := by
        intro hroof
        have hfinishNotEssential :
            f.finish ∉ Gamma.essential C.oldSlice := by
          simpa only [C.legal.frontiersEssential C.oldStage] using hfinishOld
        exact Set.disjoint_left.1
          (C.legal.strictFrontierChronology C.old_lt_new)
          ⟨hroof, hfinishNotEssential⟩ hfinishNew
      by_contra hnone
      have havoidOld : Disjoint f.support C.oldSlice := by
        rw [Set.disjoint_iff_inter_eq_empty]
        exact Set.not_nonempty_iff_eq_empty.mp hnone
      have havoidRoof : Disjoint f.support (Gamma.roof C.oldSlice) :=
        Gamma.finitePath_support_disjoint_roof_of_finish_not_roof
          C.oldSlice f havoidOld hfinishNotRoof
      have hstartRoof : f.start ∈ Gamma.roof C.oldSlice := by
        change f.start ∈ Gamma.roof (C.ladder.frontier C.oldStage)
        rw [C.ladder.frontier_eq_essential_terminalFrontier
          C.legal.roofsSourceAtStages C.oldStage, Gamma.roof_essential]
        exact C.legal.roofsSourceAtStages
          (Ladder.Stage.toExtended C.oldStage) hpSource
      exact Set.disjoint_left.1 havoidRoof f.start_mem_support hstartRoof
  obtain ⟨x, hxf, hxOld⟩ := hmeetOld
  have hxNotClosed : x ∉ Q.closedSet := fun hxClosed ↦
    Set.disjoint_left.1 hp.2 hxf hxClosed
  have hxNotExceptional : x ∉ T.exceptionalComponents := fun hxExceptional ↦
    hxNotClosed (Q.exceptionalComponents_subset_closedSet hxExceptional)
  have hxNotOldExceptional : x ∉ C.deferredOldStageExceptional := by
    intro hxExceptional
    exact hxNotExceptional
      (T.excludedInitials_subset_exceptional
        (Or.inl (Or.inl hxExceptional)))
  let xi : ↑(C.oldSlice \ C.deferredOldStageExceptional) :=
    ⟨x, hxOld, hxNotOldExceptional⟩
  let E := C.deferredOldStageRealization
  let hstart : DirectedPath.Path.initial
      (Sum.inl (E.toSegmentRealization.segment xi) : Gamma.DPath) =
        (E.leftPrefix xi).finish := by
    change (E.toSegmentRealization.segment xi).start =
      (E.leftPrefix xi).finish
    exact E.toSegmentRealization.segment_start xi |>.trans
      (E.left_finish xi).symm
  let hinter : (E.leftPrefix xi).support ∩
      DirectedPath.Path.support
        (Sum.inl (E.toSegmentRealization.segment xi) : Gamma.DPath) ⊆
        {(E.leftPrefix xi).finish} := by
    change (E.leftPrefix xi).support ∩
      (E.toSegmentRealization.segment xi).support ⊆
        {(E.leftPrefix xi).finish}
    exact (E.prefix_inter xi).subset
  let appended : Gamma.DPath :=
    DirectedPath.Path.appendFinite (E.leftPrefix xi)
      (.inl (E.toSegmentRealization.segment xi))
      hstart hinter
  have happended : appended =
      (Sum.inl (E.rightPrefix xi) : Gamma.DPath) := by
    simpa only [appended] using E.append_eq xi
  have hxRight : x ∈ (E.rightPrefix xi).support := by
    have hxAppend : x ∈ appended.support := by
      dsimp only [appended]
      rw [DirectedPath.Path.support_appendFinite]
      apply Or.inl
      have hfinishx : (E.leftPrefix xi).finish = x :=
        (E.left_finish xi).trans rfl
      exact hfinishx ▸ (E.leftPrefix xi).finish_mem_support
    rw [happended] at hxAppend
    exact hxAppend
  have hrightEq : f = E.rightPrefix xi := by
    by_contra hne
    have hne' : (Sum.inl f : Gamma.DPath) ≠
        Sum.inl (E.rightPrefix xi) := fun h ↦ hne (Sum.inl.inj h)
    exact Set.disjoint_left.1
      (C.legal.warpStages (Ladder.Stage.toExtended C.newStage)
        hpSelected.1 (E.right_mem xi).1 hne')
      hxf hxRight
  exact ⟨xi, hxNotExceptional, congrArg Sum.inl hrightEq⟩

/-- Every selected-reference component surviving the joint closure belongs
to the source-faithful spliced interval row. -/
theorem outsideReference_selectedReference_subset_splicedIntervalRow
    (Q : ClosedPrior930IntervalTransaction R T) :
    outsideReference C.selectedReference Q.closedSet ⊆
      outsideReference T.splicedIntervalRow Q.closedSet := by
  intro p hp
  obtain ⟨x, hxExceptional, hpEq⟩ :=
    Q.outside_selectedReference_eq_canonical_right hp
  subst p
  exact ⟨T.canonical_right_mem_splicedIntervalRow_of_not_mem_exceptional
    x hxExceptional, hp.2⟩

/-- Conversely, any spliced-row component outside the joint closure is an
unchanged canonical later essential component. -/
theorem outsideReference_splicedIntervalRow_subset_selectedReference
    (Q : ClosedPrior930IntervalTransaction R T) :
    outsideReference T.splicedIntervalRow Q.closedSet ⊆
      outsideReference C.selectedReference Q.closedSet := by
  intro p hp
  obtain ⟨old, rfl⟩ := hp.1
  rcases old with ⟨op, hop⟩
  obtain ⟨f, rfl⟩ := T.oldReference_tight.1.finiteCharacter hop
  let old : T.oldReference := ⟨(Sum.inl f : Gamma.DPath), hop⟩
  let out : Gamma.DPath := Gamma.starPath T.oldReference_starCompatible old
  have houtMem : out ∈ T.splicedIntervalRow := ⟨old, rfl⟩
  have hfinishOut : f.finish ∈ out.support := by
    exact Gamma.support_mono_of_extends
      (Gamma.extends_starPath T.oldReference_starCompatible old)
      f.finish_mem_support
  have hfinishOld : f.finish ∈ C.oldSlice := by
    have hterminal : f.finish ∈ Gamma.terminalFrontier T.oldReference :=
      ⟨Sum.inl f, hop, rfl⟩
    simpa only [OldStageIntervalTransaction.oldReference,
      ladderReference.terminalFrontier_eq C.legal] using hterminal
  have hfinishNotClosed : f.finish ∉ Q.closedSet := fun hclosed ↦
    Set.disjoint_left.1 hp.2 hfinishOut hclosed
  have hfinishNotExceptional :
      f.finish ∉ T.exceptionalComponents := fun hexceptional ↦
    hfinishNotClosed (Q.exceptionalComponents_subset_closedSet hexceptional)
  have hfinishNotOldExceptional :
      f.finish ∉ C.deferredOldStageExceptional := by
    intro hexceptional
    exact hfinishNotExceptional
      (T.excludedInitials_subset_exceptional
        (Or.inl (Or.inl hexceptional)))
  let x : ↑(C.oldSlice \ C.deferredOldStageExceptional) :=
    ⟨f.finish, hfinishOld, hfinishNotOldExceptional⟩
  let E := C.deferredOldStageRealization
  have hcanonicalMem : (Sum.inl (E.rightPrefix x) : Gamma.DPath) ∈
      T.splicedIntervalRow :=
    T.canonical_right_mem_splicedIntervalRow_of_not_mem_exceptional
      x hfinishNotExceptional
  have hfinishRight : f.finish ∈ (E.rightPrefix x).support := by
    exact stageIntervalRealization_source_mem_rightPrefix_support E x
  have houtEq : out = Sum.inl (E.rightPrefix x) := by
    by_contra hne
    exact Set.disjoint_left.1
      (T.splicedIntervalRow_tight.1.isWarp houtMem hcanonicalMem hne)
      hfinishOut hfinishRight
  have houtEq' :
      Gamma.starPath T.oldReference_starCompatible
          ⟨(Sum.inl f : Gamma.DPath), hop⟩ =
        Sum.inl (E.rightPrefix x) := by
    simpa only [out, old] using houtEq
  refine ⟨?_, ?_⟩
  · rw [houtEq']
    exact E.right_mem x
  · rw [houtEq']
    rw [houtEq'] at hp
    exact hp.2

/-- The two reference families are literally equal after pruning by the
joint old-stage closed carrier. -/
theorem outsideReference_splicedIntervalRow_eq_selectedReference
    (Q : ClosedPrior930IntervalTransaction R T) :
    outsideReference T.splicedIntervalRow Q.closedSet =
      outsideReference C.selectedReference Q.closedSet := by
  exact Set.Subset.antisymm
    Q.outsideReference_splicedIntervalRow_subset_selectedReference
    Q.outsideReference_selectedReference_subset_splicedIntervalRow

/-- The exact pruned equality supplies the macro-owned Theorem 4.12
assignment on the source-faithful old-reference/interval row. -/
theorem exists_outsideMacroFullAssignment
    (Q : ClosedPrior930IntervalTransaction R T) :
    Nonempty (OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := T.splicedIntervalRow)
      (X := Q.closedSet)) := by
  apply LinkageBlueprint.exists_outsideMacroFullAssignment
    T.splicedIntervalRow_tight.1.isWarp
    T.splicedIntervalRow_tight.1.finiteCharacter
    C.selectedReference_isWarp C.selectedReference_finiteCharacter
    Q.outsideReference_selectedReference_subset_splicedIntervalRow
    Q.reference_closed

/-- After pruning by the joint old-stage closed carrier, the source domain
uncovered by the selected reference is empty.  This is stronger than the
source-location hypothesis used by the generic Claim 2 compiler: it follows
from the literal equality of the two pruned reference families. -/
theorem outsideMacroSource_eq_empty
    (Q : ClosedPrior930IntervalTransaction R T) :
    Gamma.initialSet
          (outsideReference T.splicedIntervalRow Q.closedSet) \
        Gamma.initialSet C.selectedReference = ∅ := by
  ext x
  constructor
  · intro hx
    have hxout : x ∈ Gamma.initialSet
        (outsideReference C.selectedReference Q.closedSet) := by
      rw [← Q.outsideReference_splicedIntervalRow_eq_selectedReference]
      exact hx.1
    exact (hx.2 (initialSet_outsideReference_subset hxout)).elim
  · intro hx
    exact hx.elim

/-- End-to-end positive Claim 2 for the dependency-correct prior-stage
transaction.  No endpoint-clean inference and no boundary-location premise is
needed: the exact pruned-family equality makes the assignment source domain
empty, so both the finite imaginary-edge and infinite popularity conclusions
are unconditional. -/
theorem classifiedOutsideMacroFullAssignment
    (Q : ClosedPrior930IntervalTransaction R T)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := T.splicedIntervalRow)
      (X := Q.closedSet))
    {persistent : Set V} :
    (∀ s v, (A.assignment.assigned s).terminal? = some v →
        IsImaginaryEdge Gamma C.selectedReference kappa s.1 v) ∧
      (∀ s, (A.assignment.assigned s).IsInfinite →
        IsPopular Gamma C.selectedReference persistent kappa s.1) := by
  constructor
  · intro s v hterminal
    have hs : s.1 ∈ (∅ : Set V) :=
      (congrArg (fun S : Set V ↦ s.1 ∈ S)
        Q.outsideMacroSource_eq_empty).mp s.property
    exact hs.elim
  · intro s hinfinite
    have hs : s.1 ∈ (∅ : Set V) :=
      (congrArg (fun S : Set V ↦ s.1 ∈ S)
        Q.outsideMacroSource_eq_empty).mp s.property
    exact hs.elim

/-- Choose the macro assignment and return its unconditional Claim 2
classification. -/
theorem exists_classifiedOutsideMacroFullAssignment
    (Q : ClosedPrior930IntervalTransaction R T)
    {persistent : Set V} :
    ∃ A : OutsideMacroFullAssignment
        (Y := C.selectedReference) (W := T.splicedIntervalRow)
        (X := Q.closedSet),
      (∀ s v, (A.assignment.assigned s).terminal? = some v →
          IsImaginaryEdge Gamma C.selectedReference kappa s.1 v) ∧
        (∀ s, (A.assignment.assigned s).IsInfinite →
          IsPopular Gamma C.selectedReference persistent kappa s.1) := by
  let A := Q.exists_outsideMacroFullAssignment.some
  exact ⟨A, Q.classifiedOutsideMacroFullAssignment A⟩

end ClosedPrior930IntervalTransaction

#print axioms
  ClosedPrior930IntervalTransaction.outsideReference_splicedIntervalRow_eq_selectedReference
#print axioms
  ClosedPrior930IntervalTransaction.outsideMacroSource_eq_empty
#print axioms
  ClosedPrior930IntervalTransaction.classifiedOutsideMacroFullAssignment
#print axioms
  ClosedPrior930IntervalTransaction.exists_classifiedOutsideMacroFullAssignment

end LinkageBlueprint
end Blueprint
end Erdos599
