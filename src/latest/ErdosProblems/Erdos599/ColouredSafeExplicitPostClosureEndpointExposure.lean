/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeExplicitPostClosureOccurrence
import ErdosProblems.Erdos599.OutsideFracturedColouredDichotomy
import ErdosProblems.Erdos599.HalfwayPostClosurePureBoundary
import ErdosProblems.Erdos599.HalfwayPostClosureSourceAbsorption

/-!
# Endpoint exposure for the explicit-stage outside-cut occurrence

Actual hole sources and finite hole terminals belong to the native closed
set.  This does not imply that they avoid the limiting reference.  If such
an endpoint is covered, whole-reference closure instead puts its complete
limiting owner in the closed set.  The final theorem records the exact
constructive alternative: either the occurrence globalizes, or it exposes
one of those concrete closed owners.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.Alternating
open _root_.Erdos599.CardinalInduction
open ColouredSafeReverseReachability
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {alpha : Ladder.Stage (succ kappa)}
variable {seed : Set V} {z s : V} {R : LimitClosure C seed}

namespace StagePostClosureIntervalTransaction

/-- Literal native survivor intervals meet the current frontier only at
their own initial vertex. -/
theorem intervalReference_source_pure
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    {p : Gamma.DPath} (hp : p ∈ T.intervalReference)
    {x : V} (hxp : x ∈ p.support)
    (hx : x ∈ (C.ladder.frontier alpha)) : x = p.initial := by
  change p ∈ SliceSegmentCore.liftStageFamily
    C.ladder alpha
      (C.ordinaryStageFamily T.current_lt.le) at hp
  rw [(C.liftStageFamily_ordinaryStageFamily T.current_lt.le)] at hp
  obtain ⟨a, rfl⟩ := hp
  let S := T.intervalRealization.toSegmentRealization
  exact Set.mem_singleton_iff.mp
    (S.segment_source a ▸
      (show x ∈ (S.segment a).support ∩ (C.ladder.frontier alpha)
        from ⟨hxp, hx⟩))

/-- Literal native survivor intervals meet the captured later frontier only
at their finite terminal. -/
theorem intervalReference_target_pure
    (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    SliceSpliceSource.MeetsOnlyAtTerminal Gamma T.intervalReference
      (C.ladder.frontier R.later.stage) :=
  SliceDeltaLift.meetsOnlyAtTerminal_liftStageFamily
    (C.ordinaryStageFamily_meetsOnlyAtTerminal T.current_lt.le)

/-- The native completed row and its outside interval reference satisfy the
canonical fractured boundary hypotheses. -/
theorem boundaryData_of_interval_purity
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet) :
    BoundaryAligned F.outside.holes.paths
        (outsideReference T.intervalReference R.closedSet) ∧
      Gamma.initialSet (outsideReference T.intervalReference R.closedSet) ⊆
        Gamma.initialSet F.outside.holes.paths := by
  apply F.boundaryData_of_pure_boundaries
    T.interval.ambientInterval_linkage.isWarp
    T.interval.ambientInterval_linkage.initialSet_eq
    T.interval.ambientInterval_linkage.terminalFrontier_subset
  · rw [T.intervalReference_isLinkageBetween.initialSet_eq]
    exact Set.sdiff_subset
  · intro p hp x hxp hx
    exact T.intervalReference_source_pure hp hxp hx
  · exact T.intervalReference_target_pure

/-- Native nonsurvivor roots are contained in the absorbed moving
reference difference. -/
theorem deferredExceptional_subset_closedSet
    (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    (C.stageExceptional alpha R.later.stage) ⊆ R.closedSet := by
  change RegularSliceSurvivors.nonsurvivorSources Gamma C.ladder
    alpha R.later.stage ⊆ R.closedSet
  exact (C.nonsurvivorSources_subset_movingReferenceDifference alpha
    R.later.stage T.current_lt.le).trans T.difference_subset

/-- Whole limiting-reference closure descends to the literal native interval
reference. -/
theorem intervalReference_closedUnderPaths
    (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    ClosedUnderPaths Gamma T.intervalReference R.closedSet := by
  intro q hq hmeet
  let qs : T.intervalReference := ⟨q, hq⟩
  obtain ⟨x, hxq, hxX⟩ := hmeet
  have howner := R.reference_closed (T.intervalReferenceOwner qs)
    (T.intervalReferenceOwner_mem qs)
    ⟨x, (T.intervalReference_subpath_owner qs).1 hxq, hxX⟩
  exact (T.intervalReference_subpath_owner qs).1.trans howner

theorem intervalReference_mem_outside_of_initial_not_mem
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    {q : Gamma.DPath} (hq : q ∈ T.intervalReference)
    (hqx : q.initial ∉ R.closedSet) :
    q ∈ outsideReference T.intervalReference R.closedSet := by
  refine ⟨hq, Set.disjoint_left.mpr ?_⟩
  intro x hxq hxX
  exact hqx (T.intervalReference_closedUnderPaths q hq
    ⟨x, hxq, hxX⟩ q.initial_mem_support)

/-- Every actual uncovered hole initial is in the native closed set. -/
theorem uncovered_initials_subset_closedSet
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideFracturedWarp T.interval.ambientInterval R.closedSet) :
    Gamma.initialSet F.holes.paths \
        Gamma.initialSet (outsideReference T.intervalReference R.closedSet) ⊆
      R.closedSet := by
  intro x hx
  by_contra hxNotX
  have hxCut := hx.1
  rw [F.initialSet_eq] at hxCut
  have hxW : x ∈ Gamma.initialSet T.interval.ambientInterval :=
    cutInitial_sdiff_subset_initialSet T.interval.ambientInterval_linkage.isWarp
      ⟨hxCut, hxNotX⟩
  have hxOld : x ∈ (C.ladder.frontier alpha) := by
    rwa [T.interval.ambientInterval_linkage.initialSet_eq] at hxW
  have hxReference : x ∈ Gamma.initialSet T.intervalReference := by
    rw [T.intervalReference_isLinkageBetween.initialSet_eq]
    exact ⟨hxOld, fun hxe ↦ hxNotX (T.deferredExceptional_subset_closedSet hxe)⟩
  obtain ⟨q, hq, hqInitial⟩ := hxReference
  apply hx.2
  refine ⟨q, T.intervalReference_mem_outside_of_initial_not_mem hq ?_, hqInitial⟩
  rwa [hqInitial]

/-- A finite endpoint of a local native occurrence which is an actual hole
terminal and is outside the local reference has already been absorbed. -/
theorem finite_terminal_mem_closedSet
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideFracturedWarp T.interval.ambientInterval R.closedSet)
    {t : V} (htHole : t ∈ Gamma.terminalFrontier F.holes.paths)
    (htLocalOff : t ∉ Gamma.vertexSet
      (outsideReference T.intervalReference R.closedSet)) :
    t ∈ R.closedSet := by
  by_contra htNotClosed
  have htCut : t ∈ CutSplit.terminalVertices
      (outsideCarrier T.interval.ambientInterval R.closedSet)
      (outsideFamilyEdges T.interval.ambientInterval R.closedSet)
      R.closedSet := by
    rw [← F.terminalFrontier_eq]
    exact htHole
  have htRowTerminal : t ∈ Gamma.terminalFrontier T.interval.ambientInterval :=
    cutTerminal_sdiff_subset_terminalFrontier
      T.interval.ambientInterval_linkage.isWarp ⟨htCut, htNotClosed⟩
  have htNew : t ∈ C.ladder.frontier R.later.stage :=
    T.interval.ambientInterval_linkage.terminalFrontier_subset htRowTerminal
  obtain ⟨p, hpLimit, htp⟩ := C.exists_limitWarp_owner_of_mem_frontier htNew
  have hpNew : p ∈ C.limitReferenceAtFrontier R.later.stage :=
    ⟨hpLimit, t, htp, htNew⟩
  by_cases hpOld : p ∈ C.limitReferenceAtFrontier alpha
  · obtain ⟨x, hxp, hxOld⟩ := hpOld.2
    obtain ⟨q, hqReference, hqTerminal, hqSupport⟩ :=
      T.exists_intervalReference_terminal_of_limitWarp_hits_frontiers
        hpLimit hxOld hxp htNew htp
    have hpDisjoint : Disjoint p.support R.closedSet := by
      apply Set.disjoint_left.2
      intro w hwp hwClosed
      have hpSubset : p.support ⊆ R.closedSet :=
        R.reference_closed p hpLimit ⟨w, hwp, hwClosed⟩
      exact htNotClosed (hpSubset htp)
    have hqOutside : q ∈ outsideReference T.intervalReference R.closedSet :=
      ⟨hqReference, hpDisjoint.mono_left hqSupport⟩
    exact htLocalOff ⟨q, hqOutside, Gamma.terminal_mem_support hqTerminal⟩
  · exact htNotClosed (T.difference_subset
      ⟨p, Or.inr ⟨hpNew, hpOld⟩, htp⟩)

/-- A covered closed endpoint carries its entire limiting owner inside the
closed set.  This is the precise residual case which cannot be retyped by
the forward-contact confinement theorem. -/
theorem exists_closed_limitOwner_of_mem_closed_of_mem_limitWarpVertex
    (R : LimitClosure C seed) {w : V} (hwClosed : w ∈ R.closedSet)
    (hwGlobal : w ∈ Gamma.vertexSet C.ladder.limitWarp) :
    ∃ p ∈ C.ladder.limitWarp,
      w ∈ p.support ∧ p.support ⊆ R.closedSet := by
  obtain ⟨p, hp, hwp⟩ := hwGlobal
  exact ⟨p, hp, hwp, R.reference_closed p hp ⟨w, hwp, hwClosed⟩⟩

/-- Resolve the global-reference endpoint alternatives for an already
selected occurrence. The input word and its optional terminal are unchanged. -/
theorem globalOccurrence_or_closedEndpointOwner
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideFracturedWarp T.interval.ambientInterval R.closedSet)
    {s : V}
    (hsHole : s ∈ Gamma.initialSet F.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference R.closedSet))
    (A : CurrentSafeOccurrence F.holes.edgeWarp
      (outsideReference T.intervalReference R.closedSet) s)
    (hterminal : ∀ t, A.terminal? = some t →
      t ∈ Gamma.terminalFrontier F.holes.paths \
        Gamma.vertexSet (outsideReference T.intervalReference R.closedSet))
    (hfinite : ∀ t, A.terminal? = some t → A.vertexSet ∩ R.closedSet ⊆ {s, t})
    (hinfinite : A.terminal? = none → A.vertexSet ∩ R.closedSet ⊆ {s}) :
    (∃ B : CurrentSafeOccurrence F.holes.edgeWarp C.ladder.limitWarp s,
      B.forwardEdges = A.forwardEdges ∧ B.vertexSet = A.vertexSet ∧
        B.terminal? = A.terminal?) ∨
      (∃ p ∈ C.ladder.limitWarp, s ∈ p.support ∧ p.support ⊆ R.closedSet) ∨
      ∃ t, A.terminal? = some t ∧
        ∃ p ∈ C.ladder.limitWarp, t ∈ p.support ∧ p.support ⊆ R.closedSet := by
  have hsClosed : s ∈ R.closedSet := T.uncovered_initials_subset_closedSet F hsHole
  by_cases hsGlobal : s ∈ Gamma.vertexSet C.ladder.limitWarp
  · exact Or.inr (Or.inl
      (exists_closed_limitOwner_of_mem_closed_of_mem_limitWarpVertex R hsClosed hsGlobal))
  · cases ht : A.terminal? with
    | none =>
        left
        obtain ⟨B, hBF, hBV, hBT⟩ :=
          T.exists_globalOccurrence F A hfinite hinfinite hsGlobal (by
            intro t h
            have hnone : (none : Option V) ≠ some t := by simp
            exact (hnone (ht.symm.trans h)).elim)
        exact ⟨B, hBF, hBV, hBT.trans ht⟩
    | some t =>
        have htData := hterminal t ht
        have htClosed : t ∈ R.closedSet := T.finite_terminal_mem_closedSet F htData.1 htData.2
        by_cases htGlobal : t ∈ Gamma.vertexSet C.ladder.limitWarp
        · exact Or.inr (Or.inr ⟨t, rfl,
            exists_closed_limitOwner_of_mem_closed_of_mem_limitWarpVertex R htClosed htGlobal⟩)
        · left
          obtain ⟨B, hBF, hBV, hBT⟩ :=
            T.exists_globalOccurrence F A hfinite hinfinite hsGlobal (by
              intro v hv
              have htv : t = v := Option.some.inj (ht.symm.trans hv)
              rwa [← htv])
          exact ⟨B, hBF, hBV, hBT.trans ht⟩

/-- Actual single-source native construction. It either yields a global
limiting-reference occurrence or identifies the concrete closed limiting
owner at a covered exposed endpoint. -/
theorem exists_globalOccurrence_or_closedEndpointOwner
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    {s : V}
    (hsHole : s ∈ Gamma.initialSet F.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference R.closedSet)) :
    ∃ A : CurrentSafeOccurrence F.outside.holes.edgeWarp
        (outsideReference T.intervalReference R.closedSet) s,
      (∀ t, A.terminal? = some t →
        t ∈ Gamma.terminalFrontier F.outside.holes.paths \
            Gamma.vertexSet (outsideReference T.intervalReference R.closedSet) ∧
          A.vertexSet ∩ R.closedSet ⊆ {s, t}) ∧
      (A.terminal? = none → A.vertexSet ∩ R.closedSet ⊆ {s}) ∧
      ¬ A.vertexSet ⊆ R.closedSet ∧
      ((∃ B : CurrentSafeOccurrence F.outside.holes.edgeWarp
          C.ladder.limitWarp s,
          B.forwardEdges = A.forwardEdges ∧
          B.vertexSet = A.vertexSet ∧ B.terminal? = A.terminal?) ∨
        (∃ p ∈ C.ladder.limitWarp,
          s ∈ p.support ∧ p.support ⊆ R.closedSet) ∨
        ∃ t, A.terminal? = some t ∧
          ∃ p ∈ C.ladder.limitWarp,
            t ∈ p.support ∧ p.support ⊆ R.closedSet) := by
  obtain ⟨hboundary, hsource⟩ := T.boundaryData_of_interval_purity F
  have hLocalWarp : Gamma.IsWarp
      (outsideReference T.intervalReference R.closedSet) :=
    outsideReference_isWarp T.intervalReference_isLinkageBetween.isWarp
  have hLocalFinite : Gamma.HasFiniteCharacter
      (outsideReference T.intervalReference R.closedSet) :=
    outsideReference_finiteCharacter T.intervalReference_isLinkageBetween.finiteCharacter
  obtain ⟨A, hfinite, hinfinite, hout⟩ :=
    F.outside.exists_safeOccurrence_avoiding_cut hboundary hLocalWarp
      hLocalFinite hsource vertexSet_outsideReference_disjoint.symm hsHole
  refine ⟨A, hfinite, hinfinite, hout, ?_⟩
  exact T.globalOccurrence_or_closedEndpointOwner F.outside hsHole A
    (fun t ht ↦ (hfinite t ht).1) (fun t ht ↦ (hfinite t ht).2) hinfinite

end StagePostClosureIntervalTransaction

#print axioms
  StagePostClosureIntervalTransaction.uncovered_initials_subset_closedSet
#print axioms
  StagePostClosureIntervalTransaction.finite_terminal_mem_closedSet
#print axioms
  StagePostClosureIntervalTransaction.globalOccurrence_or_closedEndpointOwner
#print axioms
  StagePostClosureIntervalTransaction.exists_globalOccurrence_or_closedEndpointOwner

end Erdos599.Blueprint.LinkageBlueprint

