/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingBetaSequence
import ErdosProblems.Erdos599.JointFilteredDynamicHammockClosure
import ErdosProblems.Erdos599.FiniteFilteredHammockOmegaUnion

/-!
# The moving-beta sequence with finite filtered hammock closure

This module leaves the existing moving-beta records unchanged.  A parallel
approximation record adds the finite, distinct-endpoint filtered closure,
and forgets definitionally to the original approximation.  The omega union
therefore reuses all existing moving-stage geometry while retaining the
filtered closure needed for strong shortcut edges.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- An existing stable moving-beta approximation, strengthened by the
finite filtered closure on the same carrier. -/
structure StableFilteredDynamic931Closure
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ : Set V) (P : AltPath Gamma.graph → Prop)
    extends StableDynamic931Closure C globalZ where
  finite_filtered_closed : FiniteFilteredHammockClosedUpTo Gamma
    C.ladder.limitWarp closedSet closedSet C.ladder.limitStrictRoof
      C.ladder.limitRoof P kappa

namespace StableFilteredDynamic931Closure

/-- Jointly close a seed and choose a stable club stage above `lower`. -/
theorem exists_of_seed_above
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ seed : Set V) (lower : Ladder.Stage (succ kappa))
    (P : AltPath Gamma.graph → Prop)
    (hGlobalRoof : globalZ ⊆ C.ladder.limitRoof)
    (hGlobalHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      globalZ globalZ C.ladder.limitStrictRoof C.ladder.limitRoof kappa)
    (hGlobalFiltered : FiniteFilteredHammockClosedUpTo Gamma
      C.ladder.limitWarp globalZ globalZ C.ladder.limitStrictRoof
        C.ladder.limitRoof P kappa)
    (hGlobalReferenceClosed :
      ClosedUnderPaths Gamma C.ladder.limitWarp globalZ)
    (hseedGlobal : seed ⊆ globalZ)
    (hseedCard : #seed ≤ kappa) :
    ∃ S : StableFilteredDynamic931Closure C globalZ P,
      seed ⊆ S.closedSet ∧ lower < S.stage := by
  obtain ⟨R⟩ := JointFilteredDynamicHammockClosure.exists_of_globalClosures
    Gamma C.ladder.limitWarp kappa globalZ seed C.ladder.limitStrictRoof
      C.ladder.limitRoof P C.capacity_infinite
        (C.legal.warpStages (Ladder.finalStage (succ kappa)))
        hGlobalHammocks hGlobalFiltered hGlobalReferenceClosed hseedGlobal
          hseedCard
  obtain ⟨a, haClub, hcurrentA, hstableA⟩ :=
    C.exists_stable_later_club R.closedSet R.card_le
      (R.subset_global.trans hGlobalRoof)
  let beta : Ladder.Stage (succ kappa) :=
    RegularCardinal.aboveInClub C.legal.regular C.club C.club_isClub lower a
  have hbetaClub : beta ∈ C.club :=
    RegularCardinal.aboveInClub_mem C.legal.regular C.club C.club_isClub
      lower a
  have hlowerBeta : lower < beta :=
    RegularCardinal.left_lt_aboveInClub C.legal.regular C.club C.club_isClub
      lower a
  have haBeta : a < beta :=
    RegularCardinal.right_lt_aboveInClub C.legal.regular C.club C.club_isClub
      lower a
  refine ⟨{
    closedSet := R.closedSet
    subset_global := R.subset_global
    card_le := R.card_le
    hammock_closed := R.hammock_closed
    reference_closed := R.reference_closed
    subset_limitRoof := R.subset_global.trans hGlobalRoof
    stage := beta
    stage_mem_club := hbetaClub
    current_lt_stage := hcurrentA.trans haBeta
    stable_capture := ?_
    finite_filtered_closed := R.finite_filtered_closed
  }, R.seed_subset, hlowerBeta⟩
  intro b hbetaB
  exact hstableA b (haBeta.le.trans hbetaB)

private theorem mk_union_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {A B : Set V} (hA : #A ≤ kappa) (hB : #B ≤ kappa) :
    #(A ∪ B : Set V) ≤ kappa :=
  (Cardinal.mk_union_le A B).trans
    (Cardinal.add_le_of_le C.capacity_infinite hA hB)

theorem exists_successor
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ : Set V) (P : AltPath Gamma.graph → Prop)
    (H : Ladder.Stage (succ kappa) → Set V)
    (hGlobalRoof : globalZ ⊆ C.ladder.limitRoof)
    (hGlobalHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      globalZ globalZ C.ladder.limitStrictRoof C.ladder.limitRoof kappa)
    (hGlobalFiltered : FiniteFilteredHammockClosedUpTo Gamma
      C.ladder.limitWarp globalZ globalZ C.ladder.limitStrictRoof
        C.ladder.limitRoof P kappa)
    (hGlobalReferenceClosed :
      ClosedUnderPaths Gamma C.ladder.limitWarp globalZ)
    (hHcard : ∀ a ∈ C.club, C.newStage < a → #(H a) ≤ kappa)
    (hHglobal : ∀ a ∈ C.club, C.newStage < a → H a ⊆ globalZ)
    (S : StableFilteredDynamic931Closure C globalZ P) :
    ∃ T : StableFilteredDynamic931Closure C globalZ P,
      S.closedSet ⊆ T.closedSet ∧ H S.stage ⊆ T.closedSet ∧
        S.stage < T.stage := by
  let nextSeed := S.closedSet ∪ H S.stage
  have hseedGlobal : nextSeed ⊆ globalZ :=
    Set.union_subset S.subset_global
      (hHglobal S.stage S.stage_mem_club S.current_lt_stage)
  have hseedCard : #nextSeed ≤ kappa :=
    mk_union_le C S.card_le
      (hHcard S.stage S.stage_mem_club S.current_lt_stage)
  obtain ⟨T, hseedT, hstage⟩ := exists_of_seed_above
    C globalZ nextSeed S.stage P hGlobalRoof hGlobalHammocks hGlobalFiltered
      hGlobalReferenceClosed hseedGlobal hseedCard
  exact ⟨T, Set.subset_union_left.trans hseedT,
    Set.subset_union_right.trans hseedT, hstage⟩

end StableFilteredDynamic931Closure

/-- The countable moving-beta sequence with a filtered closure witness at
every approximation. -/
structure FilteredMovingBetaOmegaClosure
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ seed : Set V) (H : Ladder.Stage (succ kappa) → Set V)
    (P : AltPath Gamma.graph → Prop) where
  approx : ℕ → StableFilteredDynamic931Closure C globalZ P
  seed_subset : seed ⊆ (approx 0).closedSet
  successor_subset : ∀ n, (approx n).closedSet ⊆ (approx (n + 1)).closedSet
  carrier_absorbed : ∀ n, H (approx n).stage ⊆ (approx (n + 1)).closedSet
  stage_strictMono : ∀ n, (approx n).stage < (approx (n + 1)).stage

namespace FilteredMovingBetaOmegaClosure

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V}
variable {H : Ladder.Stage (succ kappa) → Set V}
variable {P : AltPath Gamma.graph → Prop}

/-- Forget only the additional filtered witnesses. -/
def toMovingBetaOmegaClosure
    (R : FilteredMovingBetaOmegaClosure C globalZ seed H P) :
    MovingBetaOmegaClosure C globalZ seed H where
  approx n := (R.approx n).toStableDynamic931Closure
  seed_subset := R.seed_subset
  successor_subset := R.successor_subset
  carrier_absorbed := R.carrier_absorbed
  stage_strictMono := R.stage_strictMono

abbrev closedSet (R : FilteredMovingBetaOmegaClosure C globalZ seed H P) :
    Set V := R.toMovingBetaOmegaClosure.closedSet

theorem closedSet_finite_filtered_closed
    (R : FilteredMovingBetaOmegaClosure C globalZ seed H P) :
    FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp R.closedSet
      R.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof P kappa := by
  apply finiteFilteredHammockClosedUpTo_iUnion_of_monotone
    (fun n ↦ (R.approx n).closedSet)
  · exact R.toMovingBetaOmegaClosure.approx_mono
  · intro n
    exact (R.approx n).finite_filtered_closed

theorem exists_of_reservoir
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ seed : Set V) (H : Ladder.Stage (succ kappa) → Set V)
    (P : AltPath Gamma.graph → Prop)
    (hGlobalRoof : globalZ ⊆ C.ladder.limitRoof)
    (hGlobalHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      globalZ globalZ C.ladder.limitStrictRoof C.ladder.limitRoof kappa)
    (hGlobalFiltered : FiniteFilteredHammockClosedUpTo Gamma
      C.ladder.limitWarp globalZ globalZ C.ladder.limitStrictRoof
        C.ladder.limitRoof P kappa)
    (hGlobalReferenceClosed :
      ClosedUnderPaths Gamma C.ladder.limitWarp globalZ)
    (hseedGlobal : seed ⊆ globalZ) (hseedCard : #seed ≤ kappa)
    (hHcard : ∀ a ∈ C.club, C.newStage < a → #(H a) ≤ kappa)
    (hHglobal : ∀ a ∈ C.club, C.newStage < a → H a ⊆ globalZ) :
    Nonempty (FilteredMovingBetaOmegaClosure C globalZ seed H P) := by
  classical
  let firstExists := StableFilteredDynamic931Closure.exists_of_seed_above
    C globalZ seed C.newStage P hGlobalRoof hGlobalHammocks hGlobalFiltered
      hGlobalReferenceClosed hseedGlobal hseedCard
  let first : StableFilteredDynamic931Closure C globalZ P :=
    Classical.choose firstExists
  have hfirst : seed ⊆ first.closedSet :=
    (Classical.choose_spec firstExists).1
  let nextExists (S : StableFilteredDynamic931Closure C globalZ P) :=
    StableFilteredDynamic931Closure.exists_successor C globalZ P H hGlobalRoof
      hGlobalHammocks hGlobalFiltered hGlobalReferenceClosed hHcard hHglobal S
  let next (S : StableFilteredDynamic931Closure C globalZ P) :
      StableFilteredDynamic931Closure C globalZ P :=
    Classical.choose (nextExists S)
  have hnext (S : StableFilteredDynamic931Closure C globalZ P) :
      S.closedSet ⊆ (next S).closedSet ∧
      H S.stage ⊆ (next S).closedSet ∧ S.stage < (next S).stage :=
    Classical.choose_spec (nextExists S)
  let approx : ℕ → StableFilteredDynamic931Closure C globalZ P :=
    fun n ↦ Nat.rec first (fun _ S ↦ next S) n
  refine ⟨{
    approx := approx
    seed_subset := ?_
    successor_subset := ?_
    carrier_absorbed := ?_
    stage_strictMono := ?_
  }⟩
  · change seed ⊆ first.closedSet
    exact hfirst
  · intro n
    simpa only [approx, Nat.rec_add_one] using (hnext (approx n)).1
  · intro n
    simpa only [approx, Nat.rec_add_one] using (hnext (approx n)).2.1
  · intro n
    simpa only [approx, Nat.rec_add_one] using (hnext (approx n)).2.2

theorem exists_for_movingReferenceDifference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ seed : Set V) (P : AltPath Gamma.graph → Prop)
    (hGlobalRoof : globalZ ⊆ C.ladder.limitRoof)
    (hGlobalHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      globalZ globalZ C.ladder.limitStrictRoof C.ladder.limitRoof kappa)
    (hGlobalFiltered : FiniteFilteredHammockClosedUpTo Gamma
      C.ladder.limitWarp globalZ globalZ C.ladder.limitStrictRoof
        C.ladder.limitRoof P kappa)
    (hGlobalReferenceClosed :
      ClosedUnderPaths Gamma C.ladder.limitWarp globalZ)
    (hseedGlobal : seed ⊆ globalZ) (hseedCard : #seed ≤ kappa)
    (hDifferenceGlobal : ∀ b ∈ C.club, C.newStage < b →
      C.movingReferenceDifference C.newStage b ⊆ globalZ) :
    Nonempty (FilteredMovingBetaOmegaClosure C globalZ seed
      (fun b ↦ C.movingReferenceDifference C.newStage b) P) := by
  apply exists_of_reservoir C globalZ seed
    (fun b ↦ C.movingReferenceDifference C.newStage b) P hGlobalRoof
      hGlobalHammocks hGlobalFiltered hGlobalReferenceClosed hseedGlobal
        hseedCard
  · intro b hb hcurrent
    exact C.mk_movingReferenceDifference_le hcurrent.le C.new_mem_club hb
  · exact hDifferenceGlobal

#print axioms StableFilteredDynamic931Closure.exists_of_seed_above
#print axioms StableFilteredDynamic931Closure.exists_successor
#print axioms FilteredMovingBetaOmegaClosure.closedSet_finite_filtered_closed
#print axioms FilteredMovingBetaOmegaClosure.exists_of_reservoir
#print axioms
  FilteredMovingBetaOmegaClosure.exists_for_movingReferenceDifference

end FilteredMovingBetaOmegaClosure

end Erdos599.Blueprint.LinkageBlueprint
