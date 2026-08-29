/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointReferenceClosedCarrier
import ErdosProblems.Erdos599.ColouredSafeMovingLimit

/-!
# Endpoint-indexed closure at the actual moving club limit

Every approximation has all native, endpoint-indexed and whole-reference
closure certificates. Successors absorb the actual moving inessential
carrier before closing. The projected native sequence supplies the same
club supremum and limit-hit absorption, while endpoint closure passes to
its exact union carrier. No future interval row is an input.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointMovingStages

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

structure Approximation (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    extends ColouredSafeMovingStages.Approximation C where
  endpoint_closed : ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
    (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa closedSet

namespace Approximation

theorem exists_of_seed_above
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (seed : Set V) (lower : Stage (succ kappa))
    (hcard : #seed ≤ kappa) (hroof : seed ⊆ C.ladder.limitRoof) :
    ∃ A : Approximation C, seed ⊆ A.closedSet ∧ lower < A.stage := by
  obtain ⟨Z, hseed, hZcard, hZroof, hclosed, href, hendpoint⟩ :=
    ColouredSafeEndpointReferenceClosedCarrier.exists_captured_jointClosed_superset
      C hcard hroof
  obtain ⟨a, _haClub, hcurrentA, hstableA⟩ :=
    C.exists_stable_later_club Z hZcard hZroof
  let beta := RegularCardinal.aboveInClub C.legal.regular C.club C.club_isClub lower a
  have hlower : lower < beta :=
    RegularCardinal.left_lt_aboveInClub C.legal.regular C.club C.club_isClub lower a
  have ha : a < beta :=
    RegularCardinal.right_lt_aboveInClub C.legal.regular C.club C.club_isClub lower a
  refine ⟨{
    closedSet := Z
    card_le := hZcard
    subset_limitRoof := hZroof
    hammock_closed := hclosed
    reference_closed := href
    endpoint_closed := hendpoint
    stage := beta
    stage_mem_club :=
      RegularCardinal.aboveInClub_mem C.legal.regular C.club C.club_isClub lower a
    current_lt_stage := hcurrentA.trans ha
    stable_capture := fun b hb ↦ hstableA b (ha.le.trans hb)
  }, hseed, hlower⟩

theorem exists_successor
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (A : Approximation C) :
    ∃ B : Approximation C, A.closedSet ⊆ B.closedSet ∧
      C.movingInessentialCarrier C.newStage A.stage ⊆ B.closedSet ∧ A.stage < B.stage := by
  let seed := A.closedSet ∪ C.movingInessentialCarrier C.newStage A.stage
  have hcard : #seed ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite
      A.card_le (C.mk_movingInessentialCarrier_le A.current_lt_stage.le
        C.new_mem_club A.stage_mem_club))
  have hroof : seed ⊆ C.ladder.limitRoof :=
    Set.union_subset A.subset_limitRoof
      (C.movingInessentialCarrier_subset_limitRoof C.newStage A.stage)
  obtain ⟨B, hseed, hstage⟩ := exists_of_seed_above C seed A.stage hcard hroof
  exact ⟨B, Set.subset_union_left.trans hseed, Set.subset_union_right.trans hseed, hstage⟩

end Approximation

/-- An actual native moving sequence with endpoint closure at every stage.
The inherited `approx` is the literal projection of the enriched stages. -/
structure Sequence (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (seed : Set V)
    extends ColouredSafeMovingStages.Sequence C seed where
  endpoint_closed : ∀ n, ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
    (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa (approx n).closedSet

namespace Sequence

theorem exists_of_seed_above
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (seed : Set V)
    (lower : Stage (succ kappa))
    (hcard : #seed ≤ kappa) (hroof : seed ⊆ C.ladder.limitRoof) :
    ∃ R : Sequence C seed, lower < (R.approx 0).stage := by
  let firstExists := Approximation.exists_of_seed_above C seed lower hcard hroof
  let first : Approximation C := Classical.choose firstExists
  have hfirst : seed ⊆ first.closedSet := (Classical.choose_spec firstExists).1
  let next (A : Approximation C) : Approximation C :=
    Classical.choose (Approximation.exists_successor C A)
  have hnext (A : Approximation C) : A.closedSet ⊆ (next A).closedSet ∧
      C.movingInessentialCarrier C.newStage A.stage ⊆ (next A).closedSet ∧
      A.stage < (next A).stage := Classical.choose_spec (Approximation.exists_successor C A)
  let approx : Nat → Approximation C := fun n ↦ Nat.rec first (fun _ A ↦ next A) n
  refine ⟨{
    approx := fun n ↦ (approx n).toApproximation
    seed_subset := hfirst
    successor_subset := fun n ↦ (hnext (approx n)).1
    carrier_absorbed := fun n ↦ (hnext (approx n)).2.1
    stage_strictMono := fun n ↦ (hnext (approx n)).2.2
    endpoint_closed := fun n ↦ (approx n).endpoint_closed
  }, (Classical.choose_spec firstExists).2⟩

end Sequence

/-- The old moving limit, on the exact same set and later stage, with the
additional endpoint-dependent hammock certificates needed by the assignment. -/
structure LimitClosure (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (seed : Set V)
    extends ColouredSafeMovingStages.LimitClosure C seed where
  endpoint_closed : ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
    (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa closedSet

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}

theorem Sequence.closedSet_endpoint_closed (R : Sequence C seed) :
    ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa
      R.toSequence.closedSet :=
  ColouredSafeEndpointHammock.Closed.iUnion_nat R.toSequence.approx_mono R.endpoint_closed

theorem Sequence.exists_limitClosure_above (R : Sequence C seed)
    (lower : Stage (succ kappa)) (hlower : lower ≤ R.toSequence.stageIndex 0) :
    ∃ U : LimitClosure C seed, lower < U.later.stage := by
  obtain ⟨U, hset, hstage⟩ := R.toSequence.exists_limitClosure_eq_above lower hlower
  refine ⟨{ toLimitClosure := U, endpoint_closed := ?_ }, hstage⟩
  rw [hset]
  exact R.closedSet_endpoint_closed

/-- The entire enriched moving closure is produced from the original small
seed, not from a row whose cut-avoidance certificates could be invalidated. -/
theorem LimitClosure.exists_of_seed_above
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (seed : Set V)
    (lower : Stage (succ kappa))
    (hcard : #seed ≤ kappa) (hroof : seed ⊆ C.ladder.limitRoof) :
    ∃ U : LimitClosure C seed, lower < U.later.stage := by
  obtain ⟨R, hR⟩ := Sequence.exists_of_seed_above C seed lower hcard hroof
  exact R.exists_limitClosure_above lower hR.le

theorem LimitClosure.exists_of_seed
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (seed : Set V)
    (hcard : #seed ≤ kappa) (hroof : seed ⊆ C.ladder.limitRoof) :
    Nonempty (LimitClosure C seed) := by
  obtain ⟨U, _hU⟩ := exists_of_seed_above C seed C.newStage hcard hroof
  exact ⟨U⟩

#print axioms Approximation.exists_of_seed_above
#print axioms Approximation.exists_successor
#print axioms Sequence.exists_of_seed_above
#print axioms Sequence.closedSet_endpoint_closed
#print axioms LimitClosure.exists_of_seed_above
#print axioms LimitClosure.exists_of_seed

end Erdos599.Blueprint.ColouredSafeEndpointMovingStages
