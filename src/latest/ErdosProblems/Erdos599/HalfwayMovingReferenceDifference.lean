/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingGlobalReferenceRoof
import ErdosProblems.Erdos599.HalfwayDeferredReferenceRoofIncidence
import ErdosProblems.Erdos599.HalfwayGlobalLocalReferenceTransport

/-!
# The small moving reference difference in Assertion 9.31

For two club frontiers `a ≤ b`, the limiting-reference members which hit
exactly one frontier form a `kappa`-small family.  The proof does not bound
either frontier.  A component which misses a frontier after its initial is
already roofed there is owned by the bounded inessential accumulated family.
The remaining components were born at markers and are owned by the bounded
marker-starting family at the later stage.

Taking supports gives the literal set `H_b` inserted by the source's
countable `(X_i, beta_i)` closing construction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

/-- Members of the global limiting reference which hit one ladder
frontier. -/
def limitReferenceAtFrontier
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) : Set Gamma.DPath :=
  referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier a)

/-- A limiting component which misses `a` although its initial vertex is
already roofed at `a`. -/
def roofedLimitReferenceMiss
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) : Set Gamma.DPath :=
  {p | p ∈ C.ladder.limitWarp ∧
    p.initial ∈ Gamma.roof (C.ladder.frontier a) ∧
    p ∉ C.limitReferenceAtFrontier a}

/-- The source's literal `H_b`: supports of limiting-reference members
which hit exactly one of the two displayed frontiers. -/
def movingReferenceDifference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a b : Ladder.Stage (succ kappa)) : Set V :=
  Gamma.vertexSet
    ((C.limitReferenceAtFrontier a \ C.limitReferenceAtFrontier b) ∪
      (C.limitReferenceAtFrontier b \ C.limitReferenceAtFrontier a))

private theorem hit_of_essential_prefix
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa))
    {p q : Gamma.DPath} (hp : p ∈ C.ladder.limitWarp)
    (hq : q ∈ ladderReference C.ladder a)
    (hqp : Gamma.Extends q p) :
    p ∈ C.limitReferenceAtFrontier a := by
  obtain ⟨f, rfl⟩ := ladderReference.finiteCharacter hq
  have hfinish : f.finish ∈ C.ladder.frontier a := by
    rw [← ladderReference.terminalFrontier_eq C.legal]
    exact ⟨Sum.inl f, hq, rfl⟩
  refine ⟨hp, ?_⟩
  exact ⟨f.finish,
    Gamma.support_mono_of_extends hqp f.finish_mem_support, hfinish⟩

/-- A roofed limiting component which misses a frontier has an inessential
prefix at that stage. -/
theorem exists_inessentialPrefix_of_roofedLimitReferenceMiss
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa))
    {p : Gamma.DPath} (hp : p ∈ C.roofedLimitReferenceMiss a) :
    ∃ q ∈ Gamma.inessentialPaths (C.ladder.warpAt a),
      Gamma.Extends q p := by
  obtain ⟨q, hq, hqp⟩ :=
    DWeb.KappaLadder.Deferred.exists_warpAt_prefix_of_limitComponent_initial_mem_roof
      C.legal a hp.1 hp.2.1
  refine ⟨q, Gamma.mem_inessentialPaths.2 ⟨hq, ?_⟩, hqp⟩
  intro hqEssential
  exact hp.2.2 (hit_of_essential_prefix C a hp.1 hqEssential hqp)

/-- Choose the unique accumulated inessential prefix witnessing a roofed
miss. -/
noncomputable def roofedMissOwner
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa))
    (p : C.roofedLimitReferenceMiss a) :
    Gamma.inessentialPaths (C.ladder.warpAt a) :=
  ⟨Classical.choose
      (C.exists_inessentialPrefix_of_roofedLimitReferenceMiss a p.2),
    (Classical.choose_spec
      (C.exists_inessentialPrefix_of_roofedLimitReferenceMiss a p.2)).1⟩

theorem roofedMissOwner_extends
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa))
    (p : C.roofedLimitReferenceMiss a) :
    Gamma.Extends (C.roofedMissOwner a p).1 p.1 :=
  (Classical.choose_spec
    (C.exists_inessentialPrefix_of_roofedLimitReferenceMiss a p.2)).2

theorem roofedMissOwner_injective
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) :
    Function.Injective (C.roofedMissOwner a) := by
  intro p q hpq
  apply Subtype.ext
  apply DWeb.IsWarp.eq_of_initial_eq Gamma
    (C.legal.warpStages (Ladder.finalStage (succ kappa))) p.2.1 q.2.1
  calc
    p.1.initial = (C.roofedMissOwner a p).1.initial :=
      (Gamma.extends_initial (C.roofedMissOwner_extends a p)).symm
    _ = (C.roofedMissOwner a q).1.initial := by
      rw [hpq]
    _ = q.1.initial :=
      Gamma.extends_initial (C.roofedMissOwner_extends a q)

/-- At a club stage, roofed misses form a `kappa`-small family. -/
theorem mk_roofedLimitReferenceMiss_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) (ha : a ∈ C.club) :
    #(C.roofedLimitReferenceMiss a) ≤ kappa := by
  have haNotPhi : a ∉ DWeb.KappaLadder.Deferred.phi C.ladder := by
    intro haPhi
    exact Set.disjoint_left.1 C.club_avoids_phi ha haPhi
  apply (Cardinal.mk_le_of_injective
    (C.roofedMissOwner_injective a)).trans
  exact lt_succ_iff.mp
    (DWeb.KappaLadder.Deferred.mk_inessentialWarpAt_lt_of_not_mem_phi
      C.legal a haNotPhi)

private theorem source_subset_roof_frontier
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) :
    Gamma.source ⊆ Gamma.roof (C.ladder.frontier a) := by
  rw [C.ladder.frontier_eq_essential_terminalFrontier
    C.legal.roofsSourceAtStages a, Gamma.roof_essential]
  exact C.legal.roofsSourceAtStages (Ladder.Stage.toExtended a)

/-- A limiting component hitting `a` and missing a later frontier `b` is a
roofed miss at `b`. -/
theorem forwardDifference_subset_roofedMiss
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a b : Ladder.Stage (succ kappa)} (hab : a ≤ b) :
    C.limitReferenceAtFrontier a \ C.limitReferenceAtFrontier b ⊆
      C.roofedLimitReferenceMiss b := by
  rintro p ⟨hpa, hpb⟩
  refine ⟨hpa.1, ?_, hpb⟩
  obtain ⟨x, hxp, hxa⟩ := hpa.2
  have hxb : x ∈ Gamma.roof (C.ladder.frontier b) := by
    rcases hab.lt_or_eq with hab | rfl
    · exact Gamma.roof_cut (C.legal.frontierChronology hab)
        (Gamma.subset_roof _ hxa)
    · exact Gamma.subset_roof _ hxa
  exact DWeb.KappaLadder.Deferred.limitComponent_initial_mem_roof_of_support_mem
    C.legal b hpa.1 hxp hxb

/-- The old-hit/new-miss half of `H_b` is `kappa`-small. -/
theorem mk_forwardReferenceDifference_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a b : Ladder.Stage (succ kappa)} (hab : a ≤ b)
    (hb : b ∈ C.club) :
    #(↑(C.limitReferenceAtFrontier a \ C.limitReferenceAtFrontier b)) ≤
      kappa :=
  (Cardinal.mk_subtype_mono (C.forwardDifference_subset_roofedMiss hab)).trans
    (C.mk_roofedLimitReferenceMiss_le b hb)

private noncomputable def laterHitVertex
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (b : Ladder.Stage (succ kappa))
    (p : C.limitReferenceAtFrontier b) : V :=
  Classical.choose p.2.2

private theorem laterHitVertex_mem_support
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (b : Ladder.Stage (succ kappa))
    (p : C.limitReferenceAtFrontier b) :
    C.laterHitVertex b p ∈ p.1.support :=
  (Classical.choose_spec p.2.2).1

private theorem laterHitVertex_mem_frontier
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (b : Ladder.Stage (succ kappa))
    (p : C.limitReferenceAtFrontier b) :
    C.laterHitVertex b p ∈ C.ladder.frontier b :=
  (Classical.choose_spec p.2.2).2

private noncomputable def laterHitPrefix
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (b : Ladder.Stage (succ kappa))
    (p : C.limitReferenceAtFrontier b) : ladderReference C.ladder b :=
  ⟨Classical.choose
      (ladderReference.exists_prefix_of_limitWarp_frontier_hit
        C.legal p.2.1 (C.laterHitVertex_mem_frontier b p)
          (C.laterHitVertex_mem_support b p)),
    (Classical.choose_spec
      (ladderReference.exists_prefix_of_limitWarp_frontier_hit
        C.legal p.2.1 (C.laterHitVertex_mem_frontier b p)
          (C.laterHitVertex_mem_support b p))).1⟩

private theorem laterHitPrefix_extends
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (b : Ladder.Stage (succ kappa))
    (p : C.limitReferenceAtFrontier b) :
    Gamma.Extends (C.laterHitPrefix b p).1 p.1 :=
  (Classical.choose_spec
    (ladderReference.exists_prefix_of_limitWarp_frontier_hit C.legal
      p.2.1 (C.laterHitVertex_mem_frontier b p)
        (C.laterHitVertex_mem_support b p))).2.2

/-- The part of the later-hit/earlier-miss family whose initials are
already roofed at the earlier stage. -/
def backwardRoofedPart
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a b : Ladder.Stage (succ kappa)) : Set Gamma.DPath :=
  {p | p ∈ C.limitReferenceAtFrontier b \
      C.limitReferenceAtFrontier a ∧
    p.initial ∈ Gamma.roof (C.ladder.frontier a)}

/-- The complementary part, whose initials were inserted by ladder
markers. -/
def backwardMarkerPart
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a b : Ladder.Stage (succ kappa)) : Set Gamma.DPath :=
  {p | p ∈ C.limitReferenceAtFrontier b \
      C.limitReferenceAtFrontier a ∧
    p.initial ∉ Gamma.roof (C.ladder.frontier a)}

private theorem backwardDifference_eq_parts
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a b : Ladder.Stage (succ kappa)) :
    C.limitReferenceAtFrontier b \ C.limitReferenceAtFrontier a =
      C.backwardRoofedPart a b ∪ C.backwardMarkerPart a b := by
  ext p
  by_cases hroof : p.initial ∈ Gamma.roof (C.ladder.frontier a)
  · constructor
    · intro hp
      exact Or.inl ⟨hp, hroof⟩
    · rintro (⟨hp, _⟩ | ⟨_, hpNotRoof⟩)
      · exact hp
      · exact (hpNotRoof hroof).elim
  · constructor
    · intro hp
      exact Or.inr ⟨hp, hroof⟩
    · rintro (⟨_, hpRoof⟩ | ⟨hp, _⟩)
      · exact (hroof hpRoof).elim
      · exact hp

private theorem backwardRoofedPart_subset_roofedMiss
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a b : Ladder.Stage (succ kappa)) :
    C.backwardRoofedPart a b ⊆ C.roofedLimitReferenceMiss a := by
  rintro p ⟨hp, hroof⟩
  exact ⟨hp.1.1, hroof, hp.2⟩

private noncomputable def backwardMarkerOwner
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a b : Ladder.Stage (succ kappa))
    (p : C.backwardMarkerPart a b) :
    ladderReference.markerStarting (Gamma := Gamma)
      (L := C.ladder) (a := b) := by
  refine ⟨(C.laterHitPrefix b ⟨p.1, p.2.1.1⟩).1,
    (C.laterHitPrefix b ⟨p.1, p.2.1.1⟩).2, ?_⟩
  intro hsource
  apply p.2.2
  rw [← Gamma.extends_initial
    (C.laterHitPrefix_extends b ⟨p.1, p.2.1.1⟩)]
  exact C.source_subset_roof_frontier a hsource

private theorem backwardMarkerOwner_injective
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a b : Ladder.Stage (succ kappa)) :
    Function.Injective (C.backwardMarkerOwner a b) := by
  intro p q hpq
  apply Subtype.ext
  apply DWeb.IsWarp.eq_of_initial_eq Gamma
    (C.legal.warpStages (Ladder.finalStage (succ kappa)))
      p.2.1.1.1 q.2.1.1.1
  calc
    p.1.initial = (C.backwardMarkerOwner a b p).1.initial :=
      (Gamma.extends_initial
        (C.laterHitPrefix_extends b ⟨p.1, p.2.1.1⟩)).symm
    _ = (C.backwardMarkerOwner a b q).1.initial := by rw [hpq]
    _ = q.1.initial :=
      Gamma.extends_initial
        (C.laterHitPrefix_extends b ⟨q.1, q.2.1.1⟩)

/-- The new-hit/old-miss half of `H_b` is `kappa`-small. -/
theorem mk_backwardReferenceDifference_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a b : Ladder.Stage (succ kappa)}
    (ha : a ∈ C.club) :
    #(↑(C.limitReferenceAtFrontier b \ C.limitReferenceAtFrontier a)) ≤
      kappa := by
  rw [C.backwardDifference_eq_parts a b]
  refine (Cardinal.mk_union_le _ _).trans ?_
  apply Cardinal.add_le_of_le C.capacity_infinite
  · exact (Cardinal.mk_subtype_mono
      (C.backwardRoofedPart_subset_roofedMiss a b)).trans
      (C.mk_roofedLimitReferenceMiss_le a ha)
  · exact (Cardinal.mk_le_of_injective
      (C.backwardMarkerOwner_injective a b)).trans
      (ladderReference.mk_markerStarting_le C.legal b)

/-- The path family underlying `H_b` is `kappa`-small. -/
theorem mk_movingReferenceDifference_paths_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a b : Ladder.Stage (succ kappa)} (hab : a ≤ b)
    (ha : a ∈ C.club) (hb : b ∈ C.club) :
    #(↑((C.limitReferenceAtFrontier a \ C.limitReferenceAtFrontier b) ∪
        (C.limitReferenceAtFrontier b \ C.limitReferenceAtFrontier a))) ≤
      kappa := by
  refine (Cardinal.mk_union_le _ _).trans ?_
  exact Cardinal.add_le_of_le C.capacity_infinite
    (C.mk_forwardReferenceDifference_le hab hb)
    (C.mk_backwardReferenceDifference_le ha)

/-- The literal moving symmetric-difference carrier has cardinality at
most `kappa`. -/
theorem mk_movingReferenceDifference_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {a b : Ladder.Stage (succ kappa)} (hab : a ≤ b)
    (ha : a ∈ C.club) (hb : b ∈ C.club) :
    #(C.movingReferenceDifference a b) ≤ kappa := by
  exact CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
    C.capacity_infinite _
    (C.mk_movingReferenceDifference_paths_le hab ha hb)

/-- Every moving-reference difference remains in the limiting ladder roof. -/
theorem movingReferenceDifference_subset_limitRoof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a b : Ladder.Stage (succ kappa)) :
    C.movingReferenceDifference a b ⊆ C.ladder.limitRoof := by
  rintro x ⟨p, hp, hxp⟩
  rcases hp with hp | hp
  · exact C.limitWarp_support_subset_limitRoof p hp.1.1 hxp
  · exact C.limitWarp_support_subset_limitRoof p hp.1.1 hxp

end ClubStageGeometry

#print axioms ClubStageGeometry.mk_movingReferenceDifference_le
#print axioms
  ClubStageGeometry.movingReferenceDifference_subset_limitRoof

end Erdos599.Blueprint.LinkageBlueprint
