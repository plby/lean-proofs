/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointInitialBlueprint
import ErdosProblems.Erdos599.HalfwayMovingReferenceReservoir
import ErdosProblems.Erdos599.SingularCardinal

/-!
# Moving reference differences from the genuine initial stage

The zero frontier is the original source, not an assumed member of the
avoiding club. A later-hit/zero-miss owner therefore has a marker-starting
essential prefix. This gives both the smallness bound and containment in
the actual recorded/marker reservoir. A triangle inclusion then allows an
existing moving closure to absorb the zero-to-limit difference.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry

open Set Cardinal Order DirectedPath Ladder ColouredSafeEndpointBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable (C : ClubStageGeometry Gamma Y kappa (succ kappa))

theorem initial_miss_not_source (hGamma : Gamma.IsUnhindered)
    {p : Gamma.DPath} (hp : p ∈ C.ladder.limitWarp)
    (hmiss : p ∉ C.limitReferenceAtFrontier (initialStage C)) :
    p.initial ∉ Gamma.source := by
  intro hsource
  apply hmiss
  refine ⟨hp, p.initial, p.initial_mem_support, ?_⟩
  rwa [frontier_initialStage C hGamma]

theorem initial_backwardDifference_subset_meeting_markerStarting
    (hGamma : Gamma.IsUnhindered) (b : Stage (succ kappa)) :
    C.limitReferenceAtFrontier b \ C.limitReferenceAtFrontier (initialStage C) ⊆
      Gamma.pathsMeetingFamily C.ladder.limitWarp
        (ladderReference.markerStarting (L := C.ladder) (a := b)) := by
  rintro p ⟨hp, hmiss⟩
  obtain ⟨x, hxp, hxb⟩ := hp.2
  obtain ⟨q, hq, _hqTerminal, hqp⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit C.legal hp.1 hxb hxp
  have hqSource : q.initial ∉ Gamma.source := by
    rw [Gamma.extends_initial hqp]
    exact C.initial_miss_not_source hGamma hp.1 hmiss
  refine ⟨hp.1, q, ⟨hq, hqSource⟩, ?_⟩
  apply Set.not_disjoint_iff.mpr
  refine ⟨q.initial, ?_, q.initial_mem_support⟩
  rw [Gamma.extends_initial hqp]
  exact p.initial_mem_support

theorem mk_initial_backwardReferenceDifference_le
    (hGamma : Gamma.IsUnhindered) (b : Stage (succ kappa)) :
    #(↑(C.limitReferenceAtFrontier b \ C.limitReferenceAtFrontier (initialStage C))) ≤
      kappa := by
  apply (Cardinal.mk_subtype_mono
    (C.initial_backwardDifference_subset_meeting_markerStarting hGamma b)).trans
  apply Gamma.mk_pathsMeetingFamily_le _ _
    (C.legal.warpStages (finalStage (succ kappa))) C.capacity_infinite
    (ladderReference.mk_markerStarting_le C.legal b)
  intro p _hp
  exact p.support_countable.le_aleph0.trans C.capacity_infinite

theorem mk_initial_movingReferenceDifference_le
    (hGamma : Gamma.IsUnhindered) {b : Stage (succ kappa)} (hb : b ∈ C.club) :
    #(C.movingReferenceDifference (initialStage C) b) ≤ kappa := by
  apply CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
    C.capacity_infinite
  apply (Cardinal.mk_union_le _ _).trans
  exact Cardinal.add_le_of_le C.capacity_infinite
    (C.mk_forwardReferenceDifference_le (show initialStage C ≤ b by
      change (0 : Ordinal) ≤ b.1
      exact bot_le) hb)
    (C.mk_initial_backwardReferenceDifference_le hGamma b)

theorem initial_backwardReferenceDifference_subset_markerRooted
    (hGamma : Gamma.IsUnhindered) (b : Stage (succ kappa)) :
    C.limitReferenceAtFrontier b \ C.limitReferenceAtFrontier (initialStage C) ⊆
      C.markerRootedLimitReference := by
  rintro p ⟨hp, hmiss⟩
  obtain ⟨x, hxp, hxb⟩ := hp.2
  obtain ⟨q, hq, _hqTerminal, hqp⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit C.legal hp.1 hxb hxp
  have hinit : q.initial = p.initial := Gamma.extends_initial hqp
  refine ⟨hp.1, ?_⟩
  rcases C.legal.accumulatedInitialProvenance (Stage.toExtended b) q hq.1 with
    hsource | ⟨d, _hdb, hd⟩
  · exact False.elim (C.initial_miss_not_source hGamma hp.1 hmiss (hinit ▸ hsource))
  · exact ⟨d, hd.trans (congrArg Option.some hinit)⟩

theorem initial_movingReferenceDifference_subset_reservoir
    (hGamma : Gamma.IsUnhindered) {b : Stage (succ kappa)} (hb : b ∈ C.club) :
    C.movingReferenceDifference (initialStage C) b ⊆ C.movingReferenceReservoir := by
  rintro x ⟨p, hp | hp, hxp⟩
  · exact ⟨p, C.roofedLimitReferenceMiss_mem_recorded_or_marker hb
      (C.forwardDifference_subset_roofedMiss
        (show initialStage C ≤ b by
          change (0 : Ordinal) ≤ b.1
          exact bot_le) hp), hxp⟩
  · exact ⟨p, Or.inr (C.initial_backwardReferenceDifference_subset_markerRooted hGamma b hp),
      hxp⟩

/-- This inclusion uses symmetric differences of owner families, not any
monotonicity of the frontier-hit predicate. -/
theorem movingReferenceDifference_triangle (a b c : Stage (succ kappa)) :
    C.movingReferenceDifference a c ⊆
      C.movingReferenceDifference a b ∪ C.movingReferenceDifference b c := by
  rintro x ⟨p, hp | hp, hxp⟩
  · by_cases hpb : p ∈ C.limitReferenceAtFrontier b
    · exact Or.inr ⟨p, Or.inl ⟨hpb, hp.2⟩, hxp⟩
    · exact Or.inl ⟨p, Or.inl ⟨hp.1, hpb⟩, hxp⟩
  · by_cases hpb : p ∈ C.limitReferenceAtFrontier b
    · exact Or.inl ⟨p, Or.inr ⟨hpb, hp.2⟩, hxp⟩
    · exact Or.inr ⟨p, Or.inr ⟨hp.1, hpb⟩, hxp⟩

#print axioms mk_initial_movingReferenceDifference_le
#print axioms initial_movingReferenceDifference_subset_reservoir
#print axioms movingReferenceDifference_triangle

end Erdos599.Blueprint.LinkageBlueprint.ClubStageGeometry
