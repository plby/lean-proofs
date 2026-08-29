/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFilteredMovingBetaSequence
import ErdosProblems.Erdos599.HalfwayMovingBetaLimit

/-!
# The filtered moving-beta limit

The limit record itself remains the existing `LimitMoving931GlobalClosure`.
The theorem packages it together with the finite filtered hammock closure on
its literal closing set, so existing consumers do not need a new record type.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open _root_.Erdos599.DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace FilteredMovingBetaOmegaClosure

/-- Finish a filtered moving-beta sequence at its genuine club supremum.
The first component is the unchanged public limit record; the second is the
additional filtered closure proof on that exact carrier. -/
theorem exists_limitClosure_with_finiteFiltered
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ seed : Set V} {P : AltPath Gamma.graph → Prop}
    (R : FilteredMovingBetaOmegaClosure C globalZ seed
      (fun b ↦ C.movingReferenceDifference C.newStage b) P)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure
      Gamma C.ladder C.club) :
    ∃ L : LimitMoving931GlobalClosure C globalZ seed,
      FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
        L.closedSet L.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
          P kappa := by
  let B := R.toMovingBetaOmegaClosure
  obtain ⟨a, haClub, haLUB, hindex, haLimit⟩ := B.exists_limitStage
  have hcapture := B.closedSet_captured_at_upper (fun n ↦ (hindex n).le)
  let L : LimitMoving931GlobalClosure C globalZ seed := {
    closedSet := B.closedSet
    seed_subset := B.seed_subset_closedSet
    subset_global := B.closedSet_subset_global
    card_le := B.closedSet_card_le
    hammock_closed := B.closedSet_hammock_closed
    reference_closed := B.closedSet_reference_closed
    subset_limitRoof := B.closedSet_subset_limitRoof
    later := {
      stage := a
      mem_club := haClub
      current_lt := (B.approx 0).current_lt_stage.trans (hindex 0)
      subset_roof := hcapture.1
    }
    frontier_inter := hcapture.2.1
    nonpersistent_strict := hcapture.2.2
    difference_subset :=
      B.movingReferenceDifference_subset_closedSet_at_limit
        hHit haLimit hindex haLUB
    stage_isLimit := haLimit
  }
  refine ⟨L, ?_⟩
  simpa only [L, B] using R.closedSet_finite_filtered_closed

/-- Construct and finish the filtered moving-beta sequence in one call. -/
theorem exists_limitClosure_for_movingReferenceDifference
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
      C.movingReferenceDifference C.newStage b ⊆ globalZ)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure
      Gamma C.ladder C.club) :
    ∃ L : LimitMoving931GlobalClosure C globalZ seed,
      FiniteFilteredHammockClosedUpTo Gamma C.ladder.limitWarp
        L.closedSet L.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
          P kappa := by
  obtain ⟨R⟩ := exists_for_movingReferenceDifference C globalZ seed P
    hGlobalRoof hGlobalHammocks hGlobalFiltered hGlobalReferenceClosed
      hseedGlobal hseedCard hDifferenceGlobal
  exact R.exists_limitClosure_with_finiteFiltered hHit

#print axioms
  FilteredMovingBetaOmegaClosure.exists_limitClosure_with_finiteFiltered
#print axioms
  FilteredMovingBetaOmegaClosure.exists_limitClosure_for_movingReferenceDifference

end FilteredMovingBetaOmegaClosure

end Erdos599.Blueprint.LinkageBlueprint
