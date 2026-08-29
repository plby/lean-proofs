/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReferenceClosedCarrier
import ErdosProblems.Erdos599.HalfwayMovingInessentialAbsorption

/-!
# Actual native moving-stage approximations

Close a small seed under native captured hammocks and whole limiting
reference owners, then choose a club stage which stably captures that set.
At each successor insert the preceding stage's moving difference and
inessential carrier before closing again. The future interval row is not
chosen or used here.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeMovingStages

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open ColouredSafeHammockOmegaClosure

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

structure Approximation
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) where
  closedSet : Set V
  card_le : #closedSet ≤ kappa
  subset_limitRoof : closedSet ⊆ C.ladder.limitRoof
  hammock_closed : FilteredOmegaClosed C.ladder.limitWarp
    (ColouredSafeHammock.CapturedByStageRoof C.ladder) kappa closedSet
  reference_closed : ClosedUnderPaths Gamma C.ladder.limitWarp closedSet
  stage : Stage (succ kappa)
  stage_mem_club : stage ∈ C.club
  current_lt_stage : C.newStage < stage
  stable_capture : ∀ b : Stage (succ kappa), stage ≤ b →
    closedSet ⊆ Gamma.roof (C.ladder.frontier b) ∧
    closedSet ∩ C.ladder.frontier b = closedSet ∩ C.persistent ∧
    closedSet \ C.persistent ⊆ Gamma.strictRoof (C.ladder.frontier b)

namespace Approximation

theorem exists_of_seed_above
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (seed : Set V) (lower : Stage (succ kappa))
    (hcard : #seed ≤ kappa) (hroof : seed ⊆ C.ladder.limitRoof) :
    ∃ A : Approximation C, seed ⊆ A.closedSet ∧ lower < A.stage := by
  obtain ⟨Z, hseed, hZcard, hZroof, hclosed, href, _⟩ :=
    ColouredSafeReferenceClosedCarrier.exists_captured_referenceClosed_later C hcard hroof
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
    stage := beta
    stage_mem_club :=
      RegularCardinal.aboveInClub_mem C.legal.regular C.club C.club_isClub lower a
    current_lt_stage := hcurrentA.trans ha
    stable_capture := fun b hb ↦ hstableA b (ha.le.trans hb)
  }, hseed, hlower⟩

/-- Insert the actual old stage's enlarged reference-difference carrier.
Its size and roof bounds are already proved for this club geometry. -/
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

structure Sequence
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (seed : Set V) where
  approx : Nat → Approximation C
  seed_subset : seed ⊆ (approx 0).closedSet
  successor_subset : ∀ n, (approx n).closedSet ⊆ (approx (n + 1)).closedSet
  carrier_absorbed : ∀ n,
    C.movingInessentialCarrier C.newStage (approx n).stage ⊆ (approx (n + 1)).closedSet
  stage_strictMono : ∀ n, (approx n).stage < (approx (n + 1)).stage

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
  refine ⟨⟨approx, hfirst, ?_, ?_, ?_⟩, ?_⟩
  · intro n
    exact (hnext (approx n)).1
  · intro n
    exact (hnext (approx n)).2.1
  · intro n
    exact (hnext (approx n)).2.2
  · exact (Classical.choose_spec firstExists).2

theorem exists_of_seed
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (seed : Set V)
    (hcard : #seed ≤ kappa) (hroof : seed ⊆ C.ladder.limitRoof) :
    Nonempty (Sequence C seed) := by
  obtain ⟨R, _hR⟩ := exists_of_seed_above C seed C.newStage hcard hroof
  exact ⟨R⟩

end Sequence

#print axioms Approximation.exists_of_seed_above
#print axioms Approximation.exists_successor
#print axioms Sequence.exists_of_seed_above
#print axioms Sequence.exists_of_seed

end Erdos599.Blueprint.ColouredSafeMovingStages
