/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafePostClosureReference
import ErdosProblems.Erdos599.HalfwayNativeOutsideReferenceConfinement

/-!
# Globalizing an outside-cut native occurrence over the native closure

Both moving-reference differences and later inessential limiting components
are fields of the actual native limit closure.  Consequently every global
reference contact of an outside-cut forward edge belongs to the literal
outside interval reference, and the occurrence retypes to `limitWarp`
without changing its word data.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.Alternating
open ColouredSafeReverseReachability
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z s : V}
variable {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

/-- A limiting-reference contact of the completed row outside the closed
set lies on a literal outside survivor interval. This pointwise fact does
not assume anything about the endpoints of a surrounding occurrence. -/
theorem globalContact_mem_outsideIntervalReference
    (T : NativePostClosureIntervalTransaction C seed z R)
    {w : V} (hwNotClosed : w ∉ R.closedSet)
    (hwGlobal : w ∈ Gamma.vertexSet C.ladder.limitWarp)
    (hwRow : w ∈ Gamma.vertexSet T.interval.ambientInterval) :
    w ∈ Gamma.vertexSet (outsideReference T.intervalReference R.closedSet) := by
  obtain ⟨p, hp, hwp⟩ := hwGlobal
  have hwLaterRoof : w ∈ Gamma.roof (C.ladder.frontier R.later.stage) := by
    obtain ⟨r, hr, hwr⟩ := hwRow
    exact T.interval.ambientInterval_in_outerRoof r hr hwr
  have hpInitialRoof : p.initial ∈ Gamma.roof (C.ladder.frontier R.later.stage) :=
    DWeb.KappaLadder.Deferred.limitComponent_initial_mem_roof_of_support_mem
      C.legal R.later.stage hp hwp hwLaterRoof
  have hpLater : p ∈ C.limitReferenceAtFrontier R.later.stage := by
    by_contra hpMiss
    have hpIE := C.mem_inessentialPaths_of_roofedLimitReferenceMiss
      R.later.stage ⟨hp, hpInitialRoof, hpMiss⟩
    exact hwNotClosed (R.inessential_subset ⟨p, hpIE, hwp⟩)
  have hpOld : p ∈ C.limitReferenceAtFrontier C.newStage := by
    by_contra hpMiss
    exact hwNotClosed (R.difference_subset ⟨p, Or.inr ⟨hpLater, hpMiss⟩, hwp⟩)
  obtain ⟨old, hpOldSupport, hOld⟩ := hpOld.2
  obtain ⟨later, hpLaterSupport, hLater⟩ := hpLater.2
  obtain ⟨q, hq, hwq, _hqTerminal, hqSupport⟩ :=
    T.exists_intervalReference_containing_of_limitWarp_hits_frontiers
      hp hOld hpOldSupport hLater hpLaterSupport hwp hwRow
  have hqDisjoint : Disjoint q.support R.closedSet := by
    apply Set.disjoint_left.2
    intro r hrq hrClosed
    have hpSubset : p.support ⊆ R.closedSet :=
      R.reference_closed p hp ⟨r, hqSupport hrq, hrClosed⟩
    exact hwNotClosed (hpSubset hwp)
  exact ⟨q, ⟨hq, hqDisjoint⟩, hwq⟩

/-- Actual forward-contact confinement for the native captured outside
interval reference. -/
theorem outside_forwardContactConfined
    (T : NativePostClosureIntervalTransaction C seed z R)
    (F : OutsideFracturedWarp T.interval.ambientInterval R.closedSet)
    (A : CurrentSafeOccurrence F.holes.edgeWarp
      (outsideReference T.intervalReference R.closedSet) s)
    (hfinite : ∀ t, A.terminal? = some t →
      A.vertexSet ∩ R.closedSet ⊆ {s, t})
    (hinfinite : A.terminal? = none →
      A.vertexSet ∩ R.closedSet ⊆ {s})
    (hs : s ∉ Gamma.vertexSet C.ladder.limitWarp)
    (hterminal : ∀ t, A.terminal? = some t →
      t ∉ Gamma.vertexSet C.ladder.limitWarp) :
    T.outsideIntervalGlobalReferenceEmbedding.ForwardContactConfined
      A.forwardEdges := by
  intro x y hxy
  have hxyRow : (x, y) ∈ familyEdges T.interval.ambientInterval :=
    F.occurrence_forwardEdges_subset_original A hxy
  have hends : x ∈ A.vertexSet ∧ y ∈ A.vertexSet := by
    cases A with
    | infinite Q hQ hfirst =>
        exact Q.forwardEdges_endpoints_mem_vertexSet hxy
    | finite t Q hQ hfirst hlast =>
        exact Q.forwardEdges_endpoints_mem_vertexSet hxy
  have contact_local {w : V} (hwA : w ∈ A.vertexSet)
      (hwGlobal : w ∈ Gamma.vertexSet C.ladder.limitWarp)
      (hwRow : w ∈ Gamma.vertexSet T.interval.ambientInterval) :
      w ∈ Gamma.vertexSet
        (outsideReference T.intervalReference R.closedSet) := by
    have hwNotClosed : w ∉ R.closedSet := by
      intro hwClosed
      cases ht : A.terminal? with
      | none =>
          have hws : w = s := Set.mem_singleton_iff.mp
            (hinfinite ht ⟨hwA, hwClosed⟩)
          exact hs (hws ▸ hwGlobal)
      | some t =>
          rcases hfinite t ht ⟨hwA, hwClosed⟩ with hws | hwt
          · exact hs (hws ▸ hwGlobal)
          · have hwt' : w = t := Set.mem_singleton_iff.mp hwt
            exact hterminal t ht (hwt' ▸ hwGlobal)
    exact T.globalContact_mem_outsideIntervalReference hwNotClosed hwGlobal hwRow
  constructor
  · intro hxGlobal
    exact contact_local hends.1 hxGlobal
      ((familyEdges_subset_vertexSet_prod T.interval.ambientInterval hxyRow).1)
  · intro hyGlobal
    exact contact_local hends.2 hyGlobal
      ((familyEdges_subset_vertexSet_prod T.interval.ambientInterval hxyRow).2)

/-- The actual native outside-cut occurrence promotes to the global limiting
reference, preserving its literal relation, carrier, and optional terminal. -/
theorem exists_globalOccurrence
    (T : NativePostClosureIntervalTransaction C seed z R)
    (F : OutsideFracturedWarp T.interval.ambientInterval R.closedSet)
    (A : CurrentSafeOccurrence F.holes.edgeWarp
      (outsideReference T.intervalReference R.closedSet) s)
    (hfinite : ∀ t, A.terminal? = some t →
      A.vertexSet ∩ R.closedSet ⊆ {s, t})
    (hinfinite : A.terminal? = none →
      A.vertexSet ∩ R.closedSet ⊆ {s})
    (hs : s ∉ Gamma.vertexSet C.ladder.limitWarp)
    (hterminal : ∀ t, A.terminal? = some t →
      t ∉ Gamma.vertexSet C.ladder.limitWarp) :
    ∃ B : CurrentSafeOccurrence F.holes.edgeWarp C.ladder.limitWarp s,
      B.forwardEdges = A.forwardEdges ∧
      B.vertexSet = A.vertexSet ∧
      B.terminal? = A.terminal? := by
  let hLocal : Gamma.IsWarp
      (outsideReference T.intervalReference R.closedSet) :=
    T.intervalReference_isLinkageBetween.isWarp.subset
      (outsideReference_subset
        (Y := T.intervalReference) (X := R.closedSet))
  have hconfined :
      T.outsideIntervalGlobalReferenceEmbedding.ForwardContactConfined
        A.forwardEdges :=
    T.outside_forwardContactConfined F A hfinite hinfinite hs hterminal
  let B := A.retypeReferenceEmbedding
    T.outsideIntervalGlobalReferenceEmbedding hLocal hconfined
  exact ⟨B, by simp [B], by simp [B], by simp [B]⟩

end NativePostClosureIntervalTransaction

#print axioms
  NativePostClosureIntervalTransaction.globalContact_mem_outsideIntervalReference
#print axioms
  NativePostClosureIntervalTransaction.outside_forwardContactConfined
#print axioms NativePostClosureIntervalTransaction.exists_globalOccurrence

end Erdos599.Blueprint.LinkageBlueprint
