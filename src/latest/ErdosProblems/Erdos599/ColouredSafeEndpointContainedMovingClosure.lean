/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointFullReferenceClosure
import ErdosProblems.Erdos599.ColouredSafeEndpointMovingClosure

/-!
# The actual native moving limit inside a closed carrier

Select each approximation using contained small joint closure. The exact
union equality from the existing moving-limit theorem retains containment
on the same output with endpoint closure and inessential absorption.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointMovingStages

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open ColouredSafeEndpointBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {Z : Set V}

theorem Approximation.exists_of_seed_above_within
    (hZ : ClosedCarrier C Z) (hZroof : Z ⊆ C.ladder.limitRoof)
    {seed : Set V} (lower : Stage (succ kappa))
    (hcard : #seed ≤ kappa) (hseedZ : seed ⊆ Z) :
    ∃ A : Approximation C, seed ⊆ A.closedSet ∧ A.closedSet ⊆ Z ∧ lower < A.stage := by
  obtain ⟨X, hseed, hXcard, hXZ, hclosed, href, hendpoint⟩ :=
    hZ.exists_small_jointClosed_within hcard hseedZ
  have hXroof := hXZ.trans hZroof
  obtain ⟨a, _haClub, hcurrentA, hstableA⟩ := C.exists_stable_later_club X hXcard hXroof
  let beta := RegularCardinal.aboveInClub C.legal.regular C.club C.club_isClub lower a
  have hlower : lower < beta :=
    RegularCardinal.left_lt_aboveInClub C.legal.regular C.club C.club_isClub lower a
  have ha : a < beta :=
    RegularCardinal.right_lt_aboveInClub C.legal.regular C.club C.club_isClub lower a
  exact ⟨{
    closedSet := X
    card_le := hXcard
    subset_limitRoof := hXroof
    hammock_closed := hclosed
    reference_closed := href
    endpoint_closed := hendpoint
    stage := beta
    stage_mem_club :=
      RegularCardinal.aboveInClub_mem C.legal.regular C.club C.club_isClub lower a
    current_lt_stage := hcurrentA.trans ha
    stable_capture := fun b hb ↦ hstableA b (ha.le.trans hb)
  }, hseed, hXZ, hlower⟩

theorem Approximation.exists_successor_within
    (hZ : ClosedCarrier C Z) (hZroof : Z ⊆ C.ladder.limitRoof)
    (hmove : ∀ b ∈ C.club, C.newStage < b →
      C.movingInessentialCarrier C.newStage b ⊆ Z)
    (A : Approximation C) (hAZ : A.closedSet ⊆ Z) :
    ∃ B : Approximation C, A.closedSet ⊆ B.closedSet ∧ B.closedSet ⊆ Z ∧
      C.movingInessentialCarrier C.newStage A.stage ⊆ B.closedSet ∧ A.stage < B.stage := by
  let seed := A.closedSet ∪ C.movingInessentialCarrier C.newStage A.stage
  have hcard : #seed ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le C.capacity_infinite
      A.card_le (C.mk_movingInessentialCarrier_le A.current_lt_stage.le
        C.new_mem_club A.stage_mem_club))
  have hseedZ : seed ⊆ Z := Set.union_subset hAZ
    (hmove A.stage A.stage_mem_club A.current_lt_stage)
  obtain ⟨B, hseed, hBZ, hstage⟩ :=
    exists_of_seed_above_within hZ hZroof A.stage hcard hseedZ
  exact ⟨B, Set.subset_union_left.trans hseed, hBZ,
    Set.subset_union_right.trans hseed, hstage⟩

theorem Sequence.exists_of_seed_above_within
    (hZ : ClosedCarrier C Z) (hZroof : Z ⊆ C.ladder.limitRoof)
    (hmove : ∀ b ∈ C.club, C.newStage < b →
      C.movingInessentialCarrier C.newStage b ⊆ Z)
    {seed : Set V} (lower : Stage (succ kappa))
    (hcard : #seed ≤ kappa) (hseedZ : seed ⊆ Z) :
    ∃ R : Sequence C seed, (∀ n, (R.approx n).closedSet ⊆ Z) ∧ lower < (R.approx 0).stage := by
  let Small := {A : Approximation C // A.closedSet ⊆ Z}
  obtain ⟨firstA, hfirst, hfirstZ, hlower⟩ :=
    Approximation.exists_of_seed_above_within hZ hZroof lower hcard hseedZ
  let first : Small := ⟨firstA, hfirstZ⟩
  have hsucc : ∀ A : Small, ∃ B : Small, A.1.closedSet ⊆ B.1.closedSet ∧
      C.movingInessentialCarrier C.newStage A.1.stage ⊆ B.1.closedSet ∧ A.1.stage < B.1.stage := by
    intro A
    obtain ⟨B, hAB, hBZ, hmoveB, hstage⟩ :=
      Approximation.exists_successor_within hZ hZroof hmove A.1 A.2
    exact ⟨⟨B, hBZ⟩, hAB, hmoveB, hstage⟩
  choose next hnextSubset hnextMove hnextStage using hsucc
  let approx : Nat → Small := fun n ↦ Nat.rec first (fun _ A ↦ next A) n
  exact ⟨{
    approx := fun n ↦ (approx n).1.toApproximation
    seed_subset := hfirst
    successor_subset := fun n ↦ hnextSubset (approx n)
    carrier_absorbed := fun n ↦ hnextMove (approx n)
    stage_strictMono := fun n ↦ hnextStage (approx n)
    endpoint_closed := fun n ↦ (approx n).1.endpoint_closed
  }, fun n ↦ (approx n).2, hlower⟩

/-- All existing limit fields belong to the exact contained union. -/
theorem LimitClosure.exists_of_seed_above_within
    (hZ : ClosedCarrier C Z) (hZroof : Z ⊆ C.ladder.limitRoof)
    (hmove : ∀ b ∈ C.club, C.newStage < b →
      C.movingInessentialCarrier C.newStage b ⊆ Z)
    {seed : Set V} (lower : Stage (succ kappa))
    (hcard : #seed ≤ kappa) (hseedZ : seed ⊆ Z) :
    ∃ U : LimitClosure C seed, U.closedSet ⊆ Z ∧ lower < U.later.stage := by
  obtain ⟨R, hRZ, hRlower⟩ :=
    Sequence.exists_of_seed_above_within hZ hZroof hmove lower hcard hseedZ
  obtain ⟨U, hset, hstage⟩ := R.toSequence.exists_limitClosure_eq_above lower hRlower.le
  have hUZ : U.closedSet ⊆ Z := by
    rw [hset]
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact hRZ n hn
  refine ⟨{ toLimitClosure := U, endpoint_closed := ?_ }, hUZ, hstage⟩
  rw [hset]
  exact R.closedSet_endpoint_closed

#print axioms Approximation.exists_of_seed_above_within
#print axioms Approximation.exists_successor_within
#print axioms Sequence.exists_of_seed_above_within
#print axioms LimitClosure.exists_of_seed_above_within

end Erdos599.Blueprint.ColouredSafeEndpointMovingStages
