/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingReferenceDifference

/-!
# The recorded/marker reservoir containing every moving reference difference

At a club stage outside the deferred obstruction set, an inessential
accumulated component is either already recorded or starts at the marker of
that stage.  A limiting-reference member extending such a component is the
same limiting member when the component was recorded, and is marker-rooted
in the remaining case.  The same initial-vertex provenance handles a new
frontier hit whose initial was not roofed at the earlier stage.

Thus the source's moving carrier `H_beta` is contained in the union of the
carriers of globally recorded limiting components and marker-rooted limiting
components.  This is the concrete ladder invariant needed by the countable
`(X_i, beta_i)` closure; no arbitrary reservoir-containment premise is hidden
in the proof.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

/-- Limiting-reference members which were selected by the deferred ladder
bookkeeping at some stage. -/
def recordedLimitReference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) : Set Gamma.DPath :=
  {p | p ∈ C.ladder.limitWarp ∧
    ∃ a : Ladder.Stage (succ kappa), C.ladder.chosen a = some p}

/-- Limiting-reference members whose initial vertex was inserted as a ladder
marker. -/
def markerRootedLimitReference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) : Set Gamma.DPath :=
  {p | p ∈ C.ladder.limitWarp ∧ p.initial ∈ C.ladder.markerSet}

/-- The literal recorded/marker carrier available to the moving Claim 9.31
closure. -/
def movingReferenceReservoir
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) : Set V :=
  Gamma.vertexSet
    (C.recordedLimitReference ∪ C.markerRootedLimitReference)

/-- Every path selected by the deferred bookkeeping persists literally to
the limiting warp, hence belongs to the recorded half of the reservoir. -/
theorem chosen_mem_recordedLimitReference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Ladder.Stage (succ kappa)} {p : Gamma.DPath}
    (hp : C.ladder.chosen a = some p) :
    p ∈ C.recordedLimitReference := by
  refine ⟨?_, a, hp⟩
  exact (C.legal.recordedPathsPersist a p hp
    (Ladder.finalStage (succ kappa)) (by
      change a.1 + 1 ≤ (succ kappa).ord
      exact (Order.add_one_le_iff).2 a.2)).1

/-- Every ladder marker is the initial vertex of a limiting component. -/
theorem exists_markerRootedLimitReference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Ladder.Stage (succ kappa)} {y : V}
    (hy : C.ladder.marker a = some y) :
    ∃ p ∈ C.markerRootedLimitReference, p.initial = y := by
  have hL : DWeb.KappaLadder.Deferred.HalfwayGeometry C.ladder := C.legal
  obtain ⟨p, hpLimit, hpInitial⟩ := hL.exists_limitPath_initial_of_marker hy
  refine ⟨p, ⟨hpLimit, ?_⟩, hpInitial⟩
  exact ⟨a, hy.trans (congrArg Option.some hpInitial.symm)⟩

/-- Every actual ladder marker is contained in the recorded/marker
reservoir, not merely every marker which happens to be mentioned later. -/
theorem markerSet_subset_movingReferenceReservoir
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) :
    C.ladder.markerSet ⊆ C.movingReferenceReservoir := by
  rintro y ⟨a, ha⟩
  obtain ⟨p, hp, hpy⟩ := C.exists_markerRootedLimitReference ha
  refine ⟨p, Or.inr hp, ?_⟩
  exact hpy ▸ p.initial_mem_support

/-- The complete carrier of every selected record is contained in the
reservoir. -/
theorem chosen_support_subset_movingReferenceReservoir
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Ladder.Stage (succ kappa)} {p : Gamma.DPath}
    (hp : C.ladder.chosen a = some p) :
    p.support ⊆ C.movingReferenceReservoir := by
  intro x hxp
  exact ⟨p, Or.inl (C.chosen_mem_recordedLimitReference hp), hxp⟩

/-- The canonical record/marker reservoir is already closed under whole
members of the global limiting warp.  This uses only warp disjointness: a
limiting member meeting a reservoir owner is that owner. -/
theorem movingReferenceReservoir_reference_closed
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) :
    ClosedUnderPaths Gamma C.ladder.limitWarp
      C.movingReferenceReservoir := by
  intro p hpLimit hpMeet
  obtain ⟨x, hxp, q, hqReservoir, hxq⟩ := hpMeet
  have hqLimit : q ∈ C.ladder.limitWarp := by
    rcases hqReservoir with hq | hq
    · exact hq.1
    · exact hq.1
  have hpq : p = q :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (C.legal.warpStages (Ladder.finalStage (succ kappa)))
      hpLimit hqLimit hxp hxq
  intro y hyp
  exact ⟨q, hqReservoir, hpq ▸ hyp⟩

/-- The record/marker reservoir is contained in the global ladder roof. -/
theorem movingReferenceReservoir_subset_limitRoof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) :
    C.movingReferenceReservoir ⊆ C.ladder.limitRoof := by
  rintro x ⟨p, hp, hxp⟩
  rcases hp with hp | hp
  · exact C.limitWarp_support_subset_limitRoof p hp.1 hxp
  · exact C.limitWarp_support_subset_limitRoof p hp.1 hxp

/-- The source bookkeeping formulation of reservoir containment.  It is
enough that the global closing set contains every selected record, contains
every marker, and is closed under the limiting reference. -/
theorem movingReferenceReservoir_subset_of_recorded_marker_closed
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {globalZ : Set V}
    (hrecorded : ∀ (a : Ladder.Stage (succ kappa)) (p : Gamma.DPath),
      C.ladder.chosen a = some p → p.support ⊆ globalZ)
    (hmarkers : C.ladder.markerSet ⊆ globalZ)
    (hclosed : ClosedUnderPaths Gamma C.ladder.limitWarp globalZ) :
    C.movingReferenceReservoir ⊆ globalZ := by
  rintro x ⟨p, hp, hxp⟩
  rcases hp with hp | hp
  · obtain ⟨a, ha⟩ := hp.2
    exact hrecorded a p ha hxp
  · apply hclosed p hp.1
    · exact ⟨p.initial, p.initial_mem_support, hmarkers hp.2⟩
    · exact hxp

private theorem source_subset_roof_frontier'
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) :
    Gamma.source ⊆ Gamma.roof (C.ladder.frontier a) := by
  rw [C.ladder.frontier_eq_essential_terminalFrontier
    C.legal.roofsSourceAtStages a, Gamma.roof_essential]
  exact C.legal.roofsSourceAtStages (Ladder.Stage.toExtended a)

/-- At a club stage, a limiting component with an inessential accumulated
prefix is either literally recorded or marker-rooted. -/
theorem roofedLimitReferenceMiss_mem_recorded_or_marker
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Ladder.Stage (succ kappa)} (ha : a ∈ C.club)
    {p : Gamma.DPath} (hp : p ∈ C.roofedLimitReferenceMiss a) :
    p ∈ C.recordedLimitReference ∪ C.markerRootedLimitReference := by
  let q : Gamma.inessentialPaths (C.ladder.warpAt a) :=
    C.roofedMissOwner a ⟨p, hp⟩
  have hqp : Gamma.Extends q.1 p :=
    C.roofedMissOwner_extends a ⟨p, hp⟩
  have hqLimit : q.1 ∈ C.ladder.limitWarp :=
    C.legal.mem_limitWarp_of_mem_inessential q.2
  have hqpInitial : q.1.initial = p.initial :=
    Gamma.extends_initial hqp
  have hqpEq : q.1 = p := by
    apply DWeb.IsWarp.eq_of_initial_eq Gamma
      (C.legal.warpStages (Ladder.finalStage (succ kappa))) hqLimit hp.1
    exact hqpInitial
  by_cases hmarker : C.ladder.marker a = some q.1.initial
  · right
    refine ⟨hp.1, a, ?_⟩
    exact hmarker.trans (congrArg Option.some hqpInitial)
  · left
    refine ⟨hp.1, ?_⟩
    have haNotPhi :
        a ∉ DWeb.KappaLadder.Deferred.phi C.ladder := by
      intro haPhi
      exact Set.disjoint_left.1 C.club_avoids_phi ha haPhi
    have hselectable :
        q.1 ∈ DWeb.KappaLadder.Deferred.selectable C.ladder a :=
      ⟨C.legal.currentInessentialPersists a q.2, hmarker⟩
    have hrecorded : q.1 ∈
        (DWeb.KappaLadder.Deferred.bookkeeping C.ladder).recordedBefore a := by
      by_contra hnot
      apply haNotPhi
      exact ⟨q.1, hselectable, hnot⟩
    obtain ⟨b, _hba, hb⟩ := hrecorded
    refine ⟨b, ?_⟩
    change C.ladder.chosen b = some q.1 at hb
    rwa [hqpEq] at hb

/-- A limiting component which first hits the later displayed frontier is
also recorded or marker-rooted.  The roofed-initial branch is the preceding
club-stage lemma; the other branch uses actual accumulated marker
provenance of its essential later-stage prefix. -/
theorem backwardReferenceDifference_mem_recorded_or_marker
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a b : Ladder.Stage (succ kappa)} (ha : a ∈ C.club)
    {p : Gamma.DPath}
    (hp : p ∈ C.limitReferenceAtFrontier b \
      C.limitReferenceAtFrontier a) :
    p ∈ C.recordedLimitReference ∪ C.markerRootedLimitReference := by
  by_cases hroof : p.initial ∈ Gamma.roof (C.ladder.frontier a)
  · exact C.roofedLimitReferenceMiss_mem_recorded_or_marker ha
      ⟨hp.1.1, hroof, hp.2⟩
  · right
    obtain ⟨x, hxp, hxb⟩ := hp.1.2
    obtain ⟨q, hqReference, _hqTerminal, hqp⟩ :=
      ladderReference.exists_prefix_of_limitWarp_frontier_hit
        C.legal hp.1.1 hxb hxp
    have hinitial : q.initial = p.initial := Gamma.extends_initial hqp
    refine ⟨hp.1.1, ?_⟩
    rcases C.legal.accumulatedInitialProvenance
        (Ladder.Stage.toExtended b) q hqReference.1 with
      hsource | ⟨d, _hdb, hd⟩
    · exact False.elim (hroof
        (hinitial ▸ C.source_subset_roof_frontier' a hsource))
    · refine ⟨d, ?_⟩
      exact hd.trans (congrArg Option.some hinitial)

/-- Every reference member contributing to the moving symmetric difference
is in the concrete recorded/marker family. -/
theorem movingReferenceDifference_paths_subset_recorded_or_marker
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a b : Ladder.Stage (succ kappa)} (hab : a ≤ b)
    (ha : a ∈ C.club) (hb : b ∈ C.club) :
    (C.limitReferenceAtFrontier a \ C.limitReferenceAtFrontier b) ∪
        (C.limitReferenceAtFrontier b \ C.limitReferenceAtFrontier a) ⊆
      C.recordedLimitReference ∪ C.markerRootedLimitReference := by
  intro p hp
  rcases hp with hp | hp
  · exact C.roofedLimitReferenceMiss_mem_recorded_or_marker hb
      (C.forwardDifference_subset_roofedMiss hab hp)
  · exact C.backwardReferenceDifference_mem_recorded_or_marker ha hp

/-- Concrete route-A reservoir conclusion for the source's `H_b`. -/
theorem movingReferenceDifference_subset_movingReferenceReservoir
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a b : Ladder.Stage (succ kappa)} (hab : a ≤ b)
    (ha : a ∈ C.club) (hb : b ∈ C.club) :
    C.movingReferenceDifference a b ⊆ C.movingReferenceReservoir := by
  rintro x ⟨p, hp, hxp⟩
  exact ⟨p,
    C.movingReferenceDifference_paths_subset_recorded_or_marker
      hab ha hb hp,
    hxp⟩

/-- It is enough for the fixed global closing reservoir to contain the
canonical recorded/marker carrier; all moving differences from the current
stage to later club stages then lie in that reservoir. -/
theorem movingReferenceDifference_subset_of_reservoir
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {globalZ : Set V}
    (hreservoir : C.movingReferenceReservoir ⊆ globalZ) :
    ∀ b ∈ C.club, C.newStage < b →
      C.movingReferenceDifference C.newStage b ⊆ globalZ := by
  intro b hb hab
  exact (C.movingReferenceDifference_subset_movingReferenceReservoir
    hab.le C.new_mem_club hb).trans hreservoir

/-- Exact discharge of the moving-beta recursion's reservoir premise from
the three causal bookkeeping invariants carried by the paper's global
closing set. -/
theorem movingReferenceDifference_subset_of_recorded_marker_closed
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {globalZ : Set V}
    (hrecorded : ∀ (a : Ladder.Stage (succ kappa)) (p : Gamma.DPath),
      C.ladder.chosen a = some p → p.support ⊆ globalZ)
    (hmarkers : C.ladder.markerSet ⊆ globalZ)
    (hclosed : ClosedUnderPaths Gamma C.ladder.limitWarp globalZ) :
    ∀ b ∈ C.club, C.newStage < b →
      C.movingReferenceDifference C.newStage b ⊆ globalZ := by
  apply C.movingReferenceDifference_subset_of_reservoir
  exact C.movingReferenceReservoir_subset_of_recorded_marker_closed
    hrecorded hmarkers hclosed

end ClubStageGeometry

#print axioms
  ClubStageGeometry.movingReferenceDifference_subset_movingReferenceReservoir
#print axioms ClubStageGeometry.movingReferenceDifference_subset_of_reservoir
#print axioms
  ClubStageGeometry.movingReferenceDifference_subset_of_recorded_marker_closed

end Erdos599.Blueprint.LinkageBlueprint
