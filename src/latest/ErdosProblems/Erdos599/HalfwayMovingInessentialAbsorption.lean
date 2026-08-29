/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingBetaLimit
import ErdosProblems.Erdos599.DeferredCurrentRecordRoof

/-!
# Absorbing newly inessential reference components at a moving limit

An inessential member at a cofinal supremum need not have been an
inessential member at an earlier stage: a genuine limiting ray is the basic
example.  Nevertheless its *whole carrier* is already covered by the
source's moving closing construction.  If the limiting owner hits one of the
cofinal earlier frontiers, it belongs to the corresponding moving reference
difference.  If it misses that frontier, its initial has eventually entered
the frontier roof; the missed-frontier lemma then produces an inessential
stage prefix.  Deferred persistence makes that prefix a literal member of
the limiting warp, so disjointness identifies it with the whole limiting
owner.

This is the exact continuity statement needed when the omega alternation
inserts both the moving reference difference and the current inessential
carrier at every selected stage.  No finite-character assertion about the
limiting reference is used.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open _root_.Erdos599.DirectedPath Ladder

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

/-- The carrier of all accumulated components which are inessential at the
displayed stage. -/
def inessentialCarrierAt
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) : Set V :=
  Gamma.vertexSet (Gamma.inessentialPaths (C.ladder.warpAt a))

/-- An inessential stage component misses that stage's essential frontier. -/
theorem inessentialPath_not_mem_limitReferenceAtFrontier
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) {p : Gamma.DPath}
    (hp : p ∈ Gamma.inessentialPaths (C.ladder.warpAt a)) :
    p ∉ C.limitReferenceAtFrontier a := by
  intro hhit
  obtain ⟨x, hxp, hxFrontier⟩ := hhit.2
  have hxStrict :=
    DWeb.KappaLadder.Deferred.inessentialPath_support_subset_strictRoof_frontier
      C.ladder C.legal hp hxp
  exact hxStrict.2 (by
    rw [C.legal.frontiersEssential a]
    exact hxFrontier)

/-- A limiting owner whose initial is already roofed and which misses the
displayed frontier is itself, literally, an inessential accumulated member.
The usual missed-frontier lemma first gives an inessential prefix; deferred
persistence places that prefix in the limiting warp, where disjointness and
the common initial identify it with the owner. -/
theorem mem_inessentialPaths_of_roofedLimitReferenceMiss
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) {p : Gamma.DPath}
    (hp : p ∈ C.roofedLimitReferenceMiss a) :
    p ∈ Gamma.inessentialPaths (C.ladder.warpAt a) := by
  obtain ⟨q, hqInessential, hqp⟩ :=
    C.exists_inessentialPrefix_of_roofedLimitReferenceMiss a hp
  have hqLimit : q ∈ C.ladder.limitWarp :=
    C.legal.mem_limitWarp_of_mem_inessential hqInessential
  have hqpEq : q = p := by
    apply DWeb.IsWarp.eq_of_initial_eq Gamma
      (C.legal.warpStages (Ladder.finalStage (succ kappa)))
      hqLimit hp.1
    exact Gamma.extends_initial hqp
  simpa only [hqpEq] using hqInessential

/-- Every limiting owner has its initial below one member of any cofinal
family of earlier stages.  Source initials are below every stage frontier;
marker initials are below every frontier strictly after their birth. -/
theorem exists_initial_roof_along_lub
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {I : Type v} [Nonempty I]
    (index : I → Ladder.Stage (succ kappa))
    {b : Ladder.Stage (succ kappa)}
    (hLUB : IsLUB (Set.range index) b)
    {p : Gamma.DPath} (hp : p ∈ C.ladder.warpAt b) :
    ∃ i, p.initial ∈ Gamma.roof (C.ladder.frontier (index i)) := by
  rcases C.legal.accumulatedInitialProvenance
      (Ladder.Stage.toExtended b) p hp with
    hpSource | ⟨d, hdB, hdMarker⟩
  · let i : I := Classical.choice (inferInstance : Nonempty I)
    refine ⟨i, ?_⟩
    rw [C.ladder.frontier_eq_essential_terminalFrontier
      C.legal.roofsSourceAtStages, Gamma.roof_essential]
    exact C.legal.roofsSourceAtStages
      (Ladder.Stage.toExtended (index i)) hpSource
  · have hdLtB : d < b := by
      change d.1 + 1 ≤ b.1 at hdB
      change d.1 < b.1
      exact Order.add_one_le_iff.mp hdB
    obtain ⟨_, ⟨i, rfl⟩, hdi⟩ := (lt_isLUB_iff hLUB).mp hdLtB
    exact ⟨i,
      DWeb.KappaLadder.Deferred.marker_mem_roof_frontier_of_lt
        C.legal hdi hdMarker⟩

/-- Pathwise continuity for the additional inessential carrier.

The first summand is the old-versus-limit moving difference.  Otherwise a
whole owner occurs either in an earlier moving difference or literally in
an earlier inessential carrier. -/
theorem inessentialCarrierAt_subset_moving_or_earlier
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {I : Type v} [Nonempty I]
    (index : I → Ladder.Stage (succ kappa))
    {a b : Ladder.Stage (succ kappa)}
    (hLUB : IsLUB (Set.range index) b) :
    C.inessentialCarrierAt b ⊆
      C.movingReferenceDifference a b ∪
        ⋃ i, (C.movingReferenceDifference a (index i) ∪
          C.inessentialCarrierAt (index i)) := by
  rintro x ⟨p, hpInessential, hxp⟩
  have hpLimit : p ∈ C.ladder.limitWarp :=
    C.legal.mem_limitWarp_of_mem_inessential hpInessential
  have hpMissB : p ∉ C.limitReferenceAtFrontier b :=
    C.inessentialPath_not_mem_limitReferenceAtFrontier b hpInessential
  by_cases hpOld : p ∈ C.limitReferenceAtFrontier a
  · exact Or.inl ⟨p, Or.inl ⟨hpOld, hpMissB⟩, hxp⟩
  · obtain ⟨i, hpInitialRoof⟩ :=
      C.exists_initial_roof_along_lub index hLUB hpInessential.1
    by_cases hpHit : p ∈ C.limitReferenceAtFrontier (index i)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i,
        Or.inl ⟨p, Or.inr ⟨hpHit, hpOld⟩, hxp⟩⟩)
    · obtain ⟨q, hqInessential, hqp⟩ :=
        C.exists_inessentialPrefix_of_roofedLimitReferenceMiss (index i)
          ⟨hpLimit, hpInitialRoof, hpHit⟩
      have hqLimit : q ∈ C.ladder.limitWarp :=
        C.legal.mem_limitWarp_of_mem_inessential hqInessential
      have hqpEq : q = p := by
        apply DWeb.IsWarp.eq_of_initial_eq Gamma
          (C.legal.warpStages (Ladder.finalStage (succ kappa)))
          hqLimit hpLimit
        exact Gamma.extends_initial hqp
      subst q
      exact Or.inr (Set.mem_iUnion.mpr ⟨i,
        Or.inr ⟨p, hqInessential, hxp⟩⟩)

/-- The carrier inserted at a moving approximation: the ordinary reference
difference together with every component currently known to be inessential. -/
def movingInessentialCarrier
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a b : Ladder.Stage (succ kappa)) : Set V :=
  C.movingReferenceDifference a b ∪ C.inessentialCarrierAt b

/-- The augmented moving carrier is still `kappa`-small at a club stage. -/
theorem mk_movingInessentialCarrier_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a b : Ladder.Stage (succ kappa)} (hab : a ≤ b)
    (ha : a ∈ C.club) (hb : b ∈ C.club) :
    #(C.movingInessentialCarrier a b) ≤ kappa := by
  apply (Cardinal.mk_union_le _ _).trans
  apply Cardinal.add_le_of_le C.capacity_infinite
  · exact C.mk_movingReferenceDifference_le hab ha hb
  · apply DWeb.KappaLadder.Deferred.mk_vertexSet_inessentialWarpAt_le_of_not_mem_phi
      C.legal C.capacity_infinite b
    intro hbPhi
    exact Set.disjoint_left.mp C.club_avoids_phi hb hbPhi

/-- Every augmented moving carrier remains in the limiting roof. -/
theorem movingInessentialCarrier_subset_limitRoof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a b : Ladder.Stage (succ kappa)) :
    C.movingInessentialCarrier a b ⊆ C.ladder.limitRoof := by
  intro x hx
  rcases hx with hx | ⟨p, hp, hxp⟩
  · exact C.movingReferenceDifference_subset_limitRoof a b hx
  · exact C.limitWarp_support_subset_limitRoof p
      (C.legal.mem_limitWarp_of_mem_inessential hp) hxp

end ClubStageGeometry

namespace MovingBetaOmegaClosure

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V}

/-- If every approximation inserts the augmented moving carrier, then the
entire inessential carrier at the cofinal limit lies in the omega union.
This includes genuine limiting rays: they are caught by an earlier moving
difference if they cross an earlier frontier, and otherwise occur literally
as an earlier inessential component. -/
theorem inessentialCarrierAt_subset_closedSet_at_limit
    (R : MovingBetaOmegaClosure C globalZ seed
      (fun b ↦ C.movingInessentialCarrier C.newStage b))
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure
      Gamma C.ladder C.club)
    {a : Ladder.Stage (succ kappa)} (haLimit : Order.IsSuccLimit a.1)
    (hindex : ∀ n, R.stageIndex n < a)
    (hLUB : IsLUB (Set.range R.stageIndex) a) :
    C.inessentialCarrierAt a ⊆ R.closedSet := by
  intro x hx
  have hcover := C.inessentialCarrierAt_subset_moving_or_earlier
    R.stageIndex (a := C.newStage) (b := a) hLUB hx
  rcases hcover with hfinal | hearlier
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp
      (C.movingReferenceDifference_subset_iUnion_at_limit hHit R.stageIndex
        R.stageIndex_strictMono.monotone haLimit hindex hLUB
          (fun n ↦ (R.approx n).stage_mem_club) hfinal)
    exact R.carrier_subset_closedSet n (Or.inl hn)
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hearlier
    exact R.carrier_subset_closedSet n hn

end MovingBetaOmegaClosure

#print axioms ClubStageGeometry.inessentialPath_not_mem_limitReferenceAtFrontier
#print axioms ClubStageGeometry.mem_inessentialPaths_of_roofedLimitReferenceMiss
#print axioms ClubStageGeometry.exists_initial_roof_along_lub
#print axioms ClubStageGeometry.inessentialCarrierAt_subset_moving_or_earlier
#print axioms ClubStageGeometry.mk_movingInessentialCarrier_le
#print axioms ClubStageGeometry.movingInessentialCarrier_subset_limitRoof
#print axioms MovingBetaOmegaClosure.inessentialCarrierAt_subset_closedSet_at_limit

end Erdos599.Blueprint.LinkageBlueprint
