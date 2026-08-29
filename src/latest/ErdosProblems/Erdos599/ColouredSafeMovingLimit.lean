/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeMovingStages
import ErdosProblems.Erdos599.DeferredLegalLimitHitClosure

/-!
# The actual native moving closure at its club supremum

The closing set is the union of the actual native approximations, not a
coercion of the older alternating-path closure. Both moving-reference
differences and inessential carriers at the supremum are absorbed. Limit
hit closure is obtained from deferred legality rather than supplied as an
additional hypothesis. No future interval row occurs in the construction.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeMovingStages

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open ColouredSafeHammockOmegaClosure

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}

namespace Sequence

def closedSet (R : Sequence C seed) : Set V :=
  ⋃ n, (R.approx n).closedSet

theorem approx_mono (R : Sequence C seed) :
    Monotone (fun n ↦ (R.approx n).closedSet) :=
  monotone_nat_of_le_succ R.successor_subset

theorem approx_subset_closedSet (R : Sequence C seed) (n : Nat) :
    (R.approx n).closedSet ⊆ R.closedSet :=
  Set.subset_iUnion (fun n ↦ (R.approx n).closedSet) n

theorem seed_subset_closedSet (R : Sequence C seed) : seed ⊆ R.closedSet :=
  R.seed_subset.trans (R.approx_subset_closedSet 0)

theorem carrier_subset_closedSet (R : Sequence C seed) (n : Nat) :
    C.movingInessentialCarrier C.newStage (R.approx n).stage ⊆ R.closedSet :=
  (R.carrier_absorbed n).trans (R.approx_subset_closedSet (n + 1))

theorem closedSet_subset_limitRoof (R : Sequence C seed) :
    R.closedSet ⊆ C.ladder.limitRoof := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  exact (R.approx n).subset_limitRoof hxn

theorem closedSet_card_le (R : Sequence C seed) : #R.closedSet ≤ kappa := by
  let stages : ULift.{u} Nat → Set V := fun n ↦ (R.approx n.down).closedSet
  have heq : R.closedSet = ⋃ i, stages i := by
    ext x
    simp [closedSet, stages]
  rw [heq]
  refine (Cardinal.mk_iUnion_le stages).trans ?_
  apply Cardinal.mul_le_of_le C.capacity_infinite
  · simpa [Cardinal.mk_nat] using C.capacity_infinite
  · apply ciSup_le'
    intro i
    exact (R.approx i.down).card_le

theorem closedSet_reference_closed (R : Sequence C seed) :
    ClosedUnderPaths Gamma C.ladder.limitWarp R.closedSet :=
  closedUnderPaths_iUnion (fun n ↦ (R.approx n).reference_closed)

theorem closedSet_hammock_closed (R : Sequence C seed) :
    FilteredOmegaClosed C.ladder.limitWarp
      (ColouredSafeHammock.CapturedByStageRoof C.ladder) kappa R.closedSet :=
  FilteredOmegaClosed.iUnion_nat R.approx_mono (fun n ↦ (R.approx n).hammock_closed)

abbrev stageIndex (R : Sequence C seed) (n : Nat) : Stage (succ kappa) :=
  (R.approx n).stage

theorem stageIndex_strictMono (R : Sequence C seed) : StrictMono R.stageIndex :=
  strictMono_nat_of_lt_succ R.stage_strictMono

theorem exists_limitStage (R : Sequence C seed) :
    ∃ a : Stage (succ kappa), a ∈ C.club ∧
      IsLUB (Set.range R.stageIndex) a ∧
      (∀ n, R.stageIndex n < a) ∧ Order.IsSuccLimit a.1 := by
  have hNat : Cardinal.lift.{u} #Nat ≤ Cardinal.lift.{0} kappa := by
    simpa only [Cardinal.mk_nat, Cardinal.lift_aleph0] using
      (Cardinal.lift_le.mpr C.capacity_infinite :
        Cardinal.lift.{0} Cardinal.aleph0 ≤ Cardinal.lift.{0} kappa)
  obtain ⟨D⟩ := HalfwayClubRangeSup.exists_data C.capacity_infinite hNat
    C.club_isClub R.stageIndex R.stageIndex_strictMono.monotone
      (fun n ↦ (R.approx n).stage_mem_club)
  have hstrict : ∀ n, R.stageIndex n < D.supIndex := by
    intro n
    exact (R.stage_strictMono n).trans_le (D.previous_le (n + 1))
  refine ⟨D.supIndex, D.supIndex_mem, D.range_isLUB, hstrict, ?_⟩
  rcases D.attained_or_genuineLimit with ⟨n, hn⟩ | ⟨_, hlim⟩
  · exact False.elim ((hstrict n).ne hn)
  · exact hlim

theorem closedSet_captured_at_upper (R : Sequence C seed)
    {a : Stage (succ kappa)} (hupper : ∀ n, R.stageIndex n ≤ a) :
    R.closedSet ⊆ Gamma.roof (C.ladder.frontier a) ∧
    R.closedSet ∩ C.ladder.frontier a = R.closedSet ∩ C.persistent ∧
    R.closedSet \ C.persistent ⊆ Gamma.strictRoof (C.ladder.frontier a) := by
  have hcapture := fun n ↦ (R.approx n).stable_capture a (hupper n)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    exact (hcapture n).1 hxn
  · ext x
    constructor
    · rintro ⟨hx, hxa⟩
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
      have hxp : x ∈ (R.approx n).closedSet ∩ C.persistent := by
        rw [← (hcapture n).2.1]
        exact ⟨hxn, hxa⟩
      exact ⟨Set.mem_iUnion.mpr ⟨n, hxn⟩, hxp.2⟩
    · rintro ⟨hx, hxp⟩
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
      have hxa : x ∈ (R.approx n).closedSet ∩ C.ladder.frontier a := by
        rw [(hcapture n).2.1]
        exact ⟨hxn, hxp⟩
      exact ⟨Set.mem_iUnion.mpr ⟨n, hxn⟩, hxa.2⟩
  · rintro x ⟨hx, hxp⟩
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    exact (hcapture n).2.2 ⟨hxn, hxp⟩

theorem difference_subset_closedSet_at_limit (R : Sequence C seed)
    {a : Stage (succ kappa)} (haLimit : Order.IsSuccLimit a.1)
    (hindex : ∀ n, R.stageIndex n < a)
    (hLUB : IsLUB (Set.range R.stageIndex) a) :
    C.movingReferenceDifference C.newStage a ⊆ R.closedSet := by
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp
    (C.movingReferenceDifference_subset_iUnion_at_limit C.limitHitClosure
      R.stageIndex R.stageIndex_strictMono.monotone haLimit hindex hLUB
        (fun n ↦ (R.approx n).stage_mem_club) hx)
  exact R.carrier_subset_closedSet n (Or.inl hn)

theorem inessential_subset_closedSet_at_limit (R : Sequence C seed)
    {a : Stage (succ kappa)} (haLimit : Order.IsSuccLimit a.1)
    (hindex : ∀ n, R.stageIndex n < a)
    (hLUB : IsLUB (Set.range R.stageIndex) a) :
    C.inessentialCarrierAt a ⊆ R.closedSet := by
  intro x hx
  rcases C.inessentialCarrierAt_subset_moving_or_earlier
      R.stageIndex (a := C.newStage) hLUB hx with hfinal | hearlier
  · exact R.difference_subset_closedSet_at_limit haLimit hindex hLUB hfinal
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hearlier
    exact R.carrier_subset_closedSet n hn

end Sequence

/-- Native captured hammock closure and whole-reference closure at an
actual later club limit, including the inessential exceptional carrier.
The future interval linkage is not an input to any field. -/
structure LimitClosure (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (seed : Set V) where
  closedSet : Set V
  seed_subset : seed ⊆ closedSet
  card_le : #closedSet ≤ kappa
  subset_limitRoof : closedSet ⊆ C.ladder.limitRoof
  hammock_closed : FilteredOmegaClosed C.ladder.limitWarp
    (ColouredSafeHammock.CapturedByStageRoof C.ladder) kappa closedSet
  reference_closed : ClosedUnderPaths Gamma C.ladder.limitWarp closedSet
  later : LaterClubRoofCapture C closedSet
  frontier_inter : closedSet ∩ C.ladder.frontier later.stage = closedSet ∩ C.persistent
  nonpersistent_strict : closedSet \ C.persistent ⊆ Gamma.strictRoof (C.ladder.frontier later.stage)
  difference_subset : C.movingReferenceDifference C.newStage later.stage ⊆ closedSet
  inessential_subset : C.inessentialCarrierAt later.stage ⊆ closedSet
  stage_isLimit : Order.IsSuccLimit later.stage.1

/-- The limit object retains the exact union carrier. This equality lets
additional increasing-union invariants pass through the construction. -/
theorem Sequence.exists_limitClosure_eq_above (R : Sequence C seed)
    (lower : Stage (succ kappa)) (hlower : lower ≤ R.stageIndex 0) :
    ∃ U : LimitClosure C seed, U.closedSet = R.closedSet ∧ lower < U.later.stage := by
  obtain ⟨a, haClub, haLUB, hindex, haLimit⟩ := R.exists_limitStage
  have hcapture := R.closedSet_captured_at_upper (fun n ↦ (hindex n).le)
  refine ⟨{
    closedSet := R.closedSet
    seed_subset := R.seed_subset_closedSet
    card_le := R.closedSet_card_le
    subset_limitRoof := R.closedSet_subset_limitRoof
    hammock_closed := R.closedSet_hammock_closed
    reference_closed := R.closedSet_reference_closed
    later := {
      stage := a
      mem_club := haClub
      current_lt := (R.approx 0).current_lt_stage.trans (hindex 0)
      subset_roof := hcapture.1
    }
    frontier_inter := hcapture.2.1
    nonpersistent_strict := hcapture.2.2
    difference_subset := R.difference_subset_closedSet_at_limit haLimit hindex haLUB
    inessential_subset := R.inessential_subset_closedSet_at_limit haLimit hindex haLUB
    stage_isLimit := haLimit
  }, rfl, hlower.trans_lt (hindex 0)⟩

theorem Sequence.exists_limitClosure_above (R : Sequence C seed)
    (lower : Stage (succ kappa)) (hlower : lower ≤ R.stageIndex 0) :
    ∃ U : LimitClosure C seed, lower < U.later.stage := by
  obtain ⟨U, _hset, hstage⟩ := R.exists_limitClosure_eq_above lower hlower
  exact ⟨U, hstage⟩

theorem Sequence.exists_limitClosure (R : Sequence C seed) :
    Nonempty (LimitClosure C seed) := by
  obtain ⟨U, _hU⟩ := R.exists_limitClosure_above (R.stageIndex 0) le_rfl
  exact ⟨U⟩

/-- The native closure can be placed beyond any specified earlier stage.
This chronology is needed when reclosing a row chosen at a prior limit. -/
theorem LimitClosure.exists_of_seed_above
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (seed : Set V)
    (lower : Stage (succ kappa))
    (hcard : #seed ≤ kappa) (hroof : seed ⊆ C.ladder.limitRoof) :
    ∃ U : LimitClosure C seed, lower < U.later.stage := by
  obtain ⟨R, hR⟩ := Sequence.exists_of_seed_above C seed lower hcard hroof
  exact R.exists_limitClosure_above lower hR.le

/-- Construct the native moving limit from only the club geometry and a
small seed lying in the limiting roof. -/
theorem LimitClosure.exists_of_seed
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (seed : Set V)
    (hcard : #seed ≤ kappa) (hroof : seed ⊆ C.ladder.limitRoof) :
    Nonempty (LimitClosure C seed) := by
  obtain ⟨R⟩ := Sequence.exists_of_seed C seed hcard hroof
  exact R.exists_limitClosure

#print axioms Sequence.closedSet_hammock_closed
#print axioms Sequence.inessential_subset_closedSet_at_limit
#print axioms Sequence.exists_limitClosure_eq_above
#print axioms LimitClosure.exists_of_seed_above
#print axioms LimitClosure.exists_of_seed

end Erdos599.Blueprint.ColouredSafeMovingStages
