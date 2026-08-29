/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosurePointwiseReference
import ErdosProblems.Erdos599.HalfwayPostClosureOutsideReferenceEmbedding
import ErdosProblems.Erdos599.HalfwayNativeReferenceIncidence
import ErdosProblems.Erdos599.OutsideFracturedOccurrenceHammock

/-!
# Globalizing an actual outside-cut native occurrence

Once the later-stage inessential carrier has been absorbed, every limiting-
reference contact at an endpoint of a literal forward edge is visible in the
outside interval reference.  A contact owner which missed the later frontier
would be in the absorbed inessential carrier.  One which hit the later but
missed the old frontier would be in the already absorbed moving difference.
For an owner hitting both frontiers, the pointwise interval theorem supplies
the local owner through the contact.

The cut certificate is used only to show that such a global contact is not
in the closing set: a cut point of the occurrence is an exposed endpoint,
and exposed endpoints are assumed outside the global reference.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating Blueprint
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace ColouredSafeReverseReachability.CurrentSafeOccurrence

variable {current Local Global : Set Gamma.DPath} {s : V}

/-- Retype a complete native occurrence through a reference subpath
embedding, using the exact forward-contact confinement certificate. -/
def retypeReferenceEmbedding
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (hLocal : Gamma.IsWarp Local)
    (A : CurrentSafeOccurrence current Local s)
    (hconfined : E.ForwardContactConfined A.forwardEdges) :
    CurrentSafeOccurrence current Global s :=
  match A with
  | .infinite Q hQ hfirst =>
      .infinite (Q.retypeReferenceEmbedding E)
        (hQ.retypeReferenceEmbedding E hLocal hconfined) hfirst
  | .finite t Q hQ hfirst hlast =>
      .finite t (Q.retypeReferenceEmbedding E)
        (hQ.retypeReferenceEmbedding E hLocal hconfined) hfirst hlast

@[simp] theorem retypeReferenceEmbedding_forwardEdges
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (hLocal : Gamma.IsWarp Local)
    (A : CurrentSafeOccurrence current Local s)
    (hconfined : E.ForwardContactConfined A.forwardEdges) :
    (A.retypeReferenceEmbedding E hLocal hconfined).forwardEdges =
      A.forwardEdges := by
  cases A <;> rfl

@[simp] theorem retypeReferenceEmbedding_vertexSet
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (hLocal : Gamma.IsWarp Local)
    (A : CurrentSafeOccurrence current Local s)
    (hconfined : E.ForwardContactConfined A.forwardEdges) :
    (A.retypeReferenceEmbedding E hLocal hconfined).vertexSet =
      A.vertexSet := by
  cases A <;> rfl

@[simp] theorem retypeReferenceEmbedding_terminal?
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    (hLocal : Gamma.IsWarp Local)
    (A : CurrentSafeOccurrence current Local s)
    (hconfined : E.ForwardContactConfined A.forwardEdges) :
    (A.retypeReferenceEmbedding E hLocal hconfined).terminal? =
      A.terminal? := by
  cases A <;> rfl

end ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace Blueprint.LinkageBlueprint

open Ladder

variable {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z s : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}
variable {current : Set Gamma.DPath}

namespace PostClosureIntervalTransaction

/-- A global-reference vertex of the occurrence cannot lie in the cut when
the only cut vertices are its exposed endpoints and those endpoints avoid
the global reference. -/
theorem occurrence_global_vertex_not_mem_closedSet
    (A : CurrentSafeOccurrence current C.ladder.limitWarp s)
    {X : Set V}
    (hfinite : ∀ t, A.terminal? = some t → A.vertexSet ∩ X ⊆ {s, t})
    (hinfinite : A.terminal? = none → A.vertexSet ∩ X ⊆ {s})
    (hs : s ∉ Gamma.vertexSet C.ladder.limitWarp)
    (hterminal : ∀ t, A.terminal? = some t →
      t ∉ Gamma.vertexSet C.ladder.limitWarp)
    {w : V} (hwA : w ∈ A.vertexSet)
    (hwGlobal : w ∈ Gamma.vertexSet C.ladder.limitWarp) :
    w ∉ X := by
  intro hwX
  cases ht : A.terminal? with
  | none =>
      have hws : w = s := Set.mem_singleton_iff.mp
        (hinfinite ht ⟨hwA, hwX⟩)
      exact hs (hws ▸ hwGlobal)
  | some t =>
      rcases hfinite t ht ⟨hwA, hwX⟩ with hws | hwt
      · exact hs (hws ▸ hwGlobal)
      · have hwt' : w = t := Set.mem_singleton_iff.mp hwt
        exact hterminal t ht (hwt' ▸ hwGlobal)

/-- Actual forward-contact confinement for the outside interval reference.
The only added hypothesis is the proved output expected from the augmented
moving-beta construction: the inessential carrier at the selected later
stage lies in the closed set. -/
theorem outside_forwardContactConfined
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    (F : OutsideFracturedWarp T.interval.ambientInterval Rlimit.closedSet)
    (A : CurrentSafeOccurrence F.holes.edgeWarp
      (outsideReference T.intervalReference Rlimit.closedSet) s)
    (hfinite : ∀ t, A.terminal? = some t →
      A.vertexSet ∩ Rlimit.closedSet ⊆ {s, t})
    (hinfinite : A.terminal? = none →
      A.vertexSet ∩ Rlimit.closedSet ⊆ {s})
    (hs : s ∉ Gamma.vertexSet C.ladder.limitWarp)
    (hterminal : ∀ t, A.terminal? = some t →
      t ∉ Gamma.vertexSet C.ladder.limitWarp)
    (hinessential : C.inessentialCarrierAt Rlimit.later.stage ⊆
      Rlimit.closedSet) :
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
        (outsideReference T.intervalReference Rlimit.closedSet) := by
    have hwNotClosed : w ∉ Rlimit.closedSet := by
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
    obtain ⟨p, hp, hwp⟩ := hwGlobal
    have hwLaterRoof : w ∈ Gamma.roof
        (C.ladder.frontier Rlimit.later.stage) := by
      obtain ⟨r, hr, hwr⟩ := hwRow
      exact T.interval.ambientInterval_in_outerRoof r hr hwr
    have hpInitialRoof : p.initial ∈ Gamma.roof
        (C.ladder.frontier Rlimit.later.stage) :=
      DWeb.KappaLadder.Deferred.limitComponent_initial_mem_roof_of_support_mem
        C.legal Rlimit.later.stage hp hwp hwLaterRoof
    have hpLater : p ∈ C.limitReferenceAtFrontier Rlimit.later.stage := by
      by_contra hpMiss
      have hpIE := C.mem_inessentialPaths_of_roofedLimitReferenceMiss
        Rlimit.later.stage ⟨hp, hpInitialRoof, hpMiss⟩
      exact hwNotClosed (hinessential ⟨p, hpIE, hwp⟩)
    have hpOld : p ∈ C.limitReferenceAtFrontier C.newStage := by
      by_contra hpMiss
      exact hwNotClosed (Rlimit.difference_subset
        ⟨p, Or.inr ⟨hpLater, hpMiss⟩, hwp⟩)
    obtain ⟨old, hpOldSupport, hOld⟩ := hpOld.2
    obtain ⟨later, hpLaterSupport, hLater⟩ := hpLater.2
    obtain ⟨q, hq, hwq, _hqTerminal, hqSupport⟩ :=
      T.exists_intervalReference_containing_of_limitWarp_hits_frontiers
        hp hOld hpOldSupport hLater hpLaterSupport hwp hwRow
    have hqDisjoint : Disjoint q.support Rlimit.closedSet := by
      apply Set.disjoint_left.2
      intro r hrq hrClosed
      have hpSubset : p.support ⊆ Rlimit.closedSet :=
        Rlimit.reference_closed p hp ⟨r, hqSupport hrq, hrClosed⟩
      exact hwNotClosed (hpSubset hwp)
    exact ⟨q, ⟨hq, hqDisjoint⟩, hwq⟩
  constructor
  · intro hxGlobal
    exact contact_local hends.1 hxGlobal
      ((familyEdges_subset_vertexSet_prod T.interval.ambientInterval hxyRow).1)
  · intro hyGlobal
    exact contact_local hends.2 hyGlobal
      ((familyEdges_subset_vertexSet_prod T.interval.ambientInterval hxyRow).2)

/-- The actual outside-cut occurrence promotes to the global limiting
reference once the later-stage inessential carrier has been absorbed.  The
literal forward relation, carrier, and optional terminal do not change. -/
theorem exists_globalOccurrence
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    (F : OutsideFracturedWarp T.interval.ambientInterval Rlimit.closedSet)
    (A : CurrentSafeOccurrence F.holes.edgeWarp
      (outsideReference T.intervalReference Rlimit.closedSet) s)
    (hfinite : ∀ t, A.terminal? = some t →
      A.vertexSet ∩ Rlimit.closedSet ⊆ {s, t})
    (hinfinite : A.terminal? = none →
      A.vertexSet ∩ Rlimit.closedSet ⊆ {s})
    (hs : s ∉ Gamma.vertexSet C.ladder.limitWarp)
    (hterminal : ∀ t, A.terminal? = some t →
      t ∉ Gamma.vertexSet C.ladder.limitWarp)
    (hinessential : C.inessentialCarrierAt Rlimit.later.stage ⊆
      Rlimit.closedSet) :
    ∃ B : CurrentSafeOccurrence F.holes.edgeWarp C.ladder.limitWarp s,
      B.forwardEdges = A.forwardEdges ∧
      B.vertexSet = A.vertexSet ∧
      B.terminal? = A.terminal? := by
  let hLocal : Gamma.IsWarp
      (outsideReference T.intervalReference Rlimit.closedSet) :=
    T.intervalReference_isLinkageBetween.isWarp.subset
      (outsideReference_subset
        (Y := T.intervalReference) (X := Rlimit.closedSet))
  have hconfined :
      T.outsideIntervalGlobalReferenceEmbedding.ForwardContactConfined
        A.forwardEdges :=
    T.outside_forwardContactConfined F A hfinite hinfinite hs hterminal
      hinessential
  let B := A.retypeReferenceEmbedding
    T.outsideIntervalGlobalReferenceEmbedding hLocal hconfined
  exact ⟨B, by simp [B], by simp [B], by simp [B]⟩

end PostClosureIntervalTransaction

end Blueprint.LinkageBlueprint

#print axioms
  ColouredSafeReverseReachability.CurrentSafeOccurrence.retypeReferenceEmbedding
#print axioms
  Blueprint.LinkageBlueprint.PostClosureIntervalTransaction.outside_forwardContactConfined
#print axioms
  Blueprint.LinkageBlueprint.PostClosureIntervalTransaction.exists_globalOccurrence

end Erdos599
