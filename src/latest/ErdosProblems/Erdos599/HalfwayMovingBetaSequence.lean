/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingGlobalClosure
import ErdosProblems.Erdos599.HalfwaySmallSetStableCapture
import ErdosProblems.Erdos599.HalfwayMovingReferenceDifference

/-!
# The countable moving-stage closure used in Assertion 9.31

The finite interval row must be chosen only after its closing set.  On the
other hand, the symmetric-difference carrier `H beta` attached to the
chosen later stage has to be inserted into the next closing set.  The
source proof resolves this dependency by an omega sequence

`X 0, beta 0, X 1, beta 1, ...`.

This file implements exactly that countable alternation.  Each `X n` is a
genuine dynamic global-reference/hammock closure; `beta n` is a club stage
which stably captures `X n`; and `H (beta n)` is included in `X (n+1)`.
The limit union is again small, reference-closed, and hammock-closed.

The hypothesis `H beta ⊆ globalZ` for club `beta` is intentionally explicit.
It is the earlier reservoir invariant of the paper and does **not** follow
from `ClosedUnderPaths ... globalZ`: an `H beta` reference path need not meet
`globalZ`.  No future interval row is used in this construction and the
closing sets are never closed under such a row.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- One completed approximation of the moving-stage construction.  The
closed-set fields are the actual output of the dynamic 9.31 closer.  The
stage fields strengthen ordinary roof capture to stable capture on the
entire tail. -/
structure StableDynamic931Closure
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ : Set V) where
  closedSet : Set V
  subset_global : closedSet ⊆ globalZ
  card_le : #closedSet ≤ kappa
  hammock_closed : HammockClosedUpTo Gamma C.ladder.limitWarp closedSet
    closedSet C.ladder.limitStrictRoof C.ladder.limitRoof kappa
  reference_closed : ClosedUnderPaths Gamma C.ladder.limitWarp closedSet
  subset_limitRoof : closedSet ⊆ C.ladder.limitRoof
  stage : Ladder.Stage (succ kappa)
  stage_mem_club : stage ∈ C.club
  current_lt_stage : C.newStage < stage
  stable_capture : ∀ b : Ladder.Stage (succ kappa), stage ≤ b →
    closedSet ⊆ Gamma.roof (C.ladder.frontier b) ∧
    closedSet ∩ C.ladder.frontier b = closedSet ∩ C.persistent ∧
    closedSet \ C.persistent ⊆ Gamma.strictRoof (C.ladder.frontier b)

namespace StableDynamic931Closure

/-- Close a small reservoir subset and choose a stable club capture above
an arbitrary lower stage. -/
theorem exists_of_seed_above
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ seed : Set V) (lower : Ladder.Stage (succ kappa))
    (hGlobalRoof : globalZ ⊆ C.ladder.limitRoof)
    (hGlobalHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      globalZ globalZ C.ladder.limitStrictRoof C.ladder.limitRoof kappa)
    (hGlobalReferenceClosed :
      ClosedUnderPaths Gamma C.ladder.limitWarp globalZ)
    (hseedGlobal : seed ⊆ globalZ)
    (hseedCard : #seed ≤ kappa) :
    ∃ S : StableDynamic931Closure C globalZ,
      seed ⊆ S.closedSet ∧ lower < S.stage := by
  obtain ⟨R⟩ := DynamicMoving931GlobalClosure.exists_of_globalClosedSet
    C globalZ seed hGlobalRoof hGlobalHammocks hGlobalReferenceClosed
      hseedGlobal hseedCard
  obtain ⟨a, haClub, hcurrentA, hstableA⟩ :=
    C.exists_stable_later_club R.closedSet R.card_le R.subset_limitRoof
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
    subset_limitRoof := R.subset_limitRoof
    stage := beta
    stage_mem_club := hbetaClub
    current_lt_stage := hcurrentA.trans haBeta
    stable_capture := ?_
  }, R.seed_subset, hlowerBeta⟩
  intro b hbetaB
  exact hstableA b (haBeta.le.trans hbetaB)

private theorem mk_union_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {A B : Set V} (hA : #A ≤ kappa) (hB : #B ≤ kappa) :
    #(A ∪ B : Set V) ≤ kappa :=
  (Cardinal.mk_union_le A B).trans
    (Cardinal.add_le_of_le C.capacity_infinite hA hB)

/-- One sound moving-stage successor.  The new dynamic closure contains the
old approximation and the carrier belonging to the old chosen stage; its
new stable stage is strictly later. -/
theorem exists_successor
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ : Set V)
    (H : Ladder.Stage (succ kappa) → Set V)
    (hGlobalRoof : globalZ ⊆ C.ladder.limitRoof)
    (hGlobalHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      globalZ globalZ C.ladder.limitStrictRoof C.ladder.limitRoof kappa)
    (hGlobalReferenceClosed :
      ClosedUnderPaths Gamma C.ladder.limitWarp globalZ)
    (hHcard : ∀ a ∈ C.club, C.newStage < a → #(H a) ≤ kappa)
    (hHglobal : ∀ a ∈ C.club, C.newStage < a → H a ⊆ globalZ)
    (S : StableDynamic931Closure C globalZ) :
    ∃ T : StableDynamic931Closure C globalZ,
      S.closedSet ⊆ T.closedSet ∧
      H S.stage ⊆ T.closedSet ∧ S.stage < T.stage := by
  let seed := S.closedSet ∪ H S.stage
  have hseedGlobal : seed ⊆ globalZ :=
    Set.union_subset S.subset_global
      (hHglobal S.stage S.stage_mem_club S.current_lt_stage)
  have hseedCard : #seed ≤ kappa :=
    mk_union_le C S.card_le
      (hHcard S.stage S.stage_mem_club S.current_lt_stage)
  obtain ⟨T, hseedT, hstage⟩ := exists_of_seed_above
    C globalZ seed S.stage hGlobalRoof hGlobalHammocks
      hGlobalReferenceClosed hseedGlobal hseedCard
  exact ⟨T, Set.subset_union_left.trans hseedT,
    Set.subset_union_right.trans hseedT, hstage⟩

end StableDynamic931Closure

/-- The actual countable sequence.  Its limit set is defined below as the
union of the displayed approximations. -/
structure MovingBetaOmegaClosure
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ seed : Set V)
    (H : Ladder.Stage (succ kappa) → Set V) where
  approx : ℕ → StableDynamic931Closure C globalZ
  seed_subset : seed ⊆ (approx 0).closedSet
  successor_subset : ∀ n, (approx n).closedSet ⊆ (approx (n + 1)).closedSet
  carrier_absorbed : ∀ n, H (approx n).stage ⊆ (approx (n + 1)).closedSet
  stage_strictMono : ∀ n, (approx n).stage < (approx (n + 1)).stage

namespace MovingBetaOmegaClosure

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V}
variable {H : Ladder.Stage (succ kappa) → Set V}

/-- The union closing set produced before the final limit-stage argument. -/
def closedSet (R : MovingBetaOmegaClosure C globalZ seed H) : Set V :=
  ⋃ n, (R.approx n).closedSet

theorem approx_mono (R : MovingBetaOmegaClosure C globalZ seed H) :
    Monotone (fun n => (R.approx n).closedSet) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    R.successor_subset n

theorem approx_subset_closedSet (R : MovingBetaOmegaClosure C globalZ seed H)
    (n : ℕ) : (R.approx n).closedSet ⊆ R.closedSet :=
  Set.subset_iUnion (fun n => (R.approx n).closedSet) n

theorem seed_subset_closedSet (R : MovingBetaOmegaClosure C globalZ seed H) :
    seed ⊆ R.closedSet :=
  R.seed_subset.trans (R.approx_subset_closedSet 0)

theorem carrier_subset_closedSet
    (R : MovingBetaOmegaClosure C globalZ seed H) (n : ℕ) :
    H (R.approx n).stage ⊆ R.closedSet :=
  (R.carrier_absorbed n).trans (R.approx_subset_closedSet (n + 1))

theorem closedSet_subset_global
    (R : MovingBetaOmegaClosure C globalZ seed H) :
    R.closedSet ⊆ globalZ := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  exact (R.approx n).subset_global hxn

theorem closedSet_subset_limitRoof
    (R : MovingBetaOmegaClosure C globalZ seed H) :
    R.closedSet ⊆ C.ladder.limitRoof := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  exact (R.approx n).subset_limitRoof hxn

theorem closedSet_card_le
    (R : MovingBetaOmegaClosure C globalZ seed H) :
    #R.closedSet ≤ kappa := by
  let stages : ULift.{u} ℕ → Set V :=
    fun n => (R.approx n.down).closedSet
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

theorem closedSet_reference_closed
    (R : MovingBetaOmegaClosure C globalZ seed H) :
    ClosedUnderPaths Gamma C.ladder.limitWarp R.closedSet :=
  closedUnderPaths_iUnion (fun n => (R.approx n).reference_closed)

/-- At the limit, every eligible finite endpoint pair already occurs in one
common approximation.  That approximation supplies its maximal hammock,
which remains contained in the union. -/
theorem closedSet_hammock_closed
    (R : MovingBetaOmegaClosure C globalZ seed H) :
    HammockClosedUpTo Gamma C.ladder.limitWarp R.closedSet R.closedSet
      C.ladder.limitStrictRoof C.ladder.limitRoof kappa := by
  intro u e helig
  obtain ⟨nu, hnu⟩ := Set.mem_iUnion.1 helig.1.1
  cases e with
  | infinity =>
      have heligNu : HammockEligible (R.approx nu).closedSet
          C.ladder.limitStrictRoof C.ladder.limitRoof u .infinity :=
        ⟨⟨hnu, helig.1.2⟩, trivial⟩
      obtain ⟨K, hKmax, hKcontained⟩ :=
        (R.approx nu).hammock_closed u .infinity heligNu
      exact ⟨K, hKmax, hKcontained.trans (R.approx_subset_closedSet nu)⟩
  | vertex v =>
      obtain ⟨nv, hnv⟩ := Set.mem_iUnion.1 helig.2.1
      let n := max nu nv
      have hun : u ∈ (R.approx n).closedSet :=
        R.approx_mono (Nat.le_max_left nu nv) hnu
      have hvn : v ∈ (R.approx n).closedSet :=
        R.approx_mono (Nat.le_max_right nu nv) hnv
      have heligN : HammockEligible (R.approx n).closedSet
          C.ladder.limitStrictRoof C.ladder.limitRoof u (.vertex v) :=
        ⟨⟨hun, helig.1.2⟩, ⟨hvn, helig.2.2⟩⟩
      obtain ⟨K, hKmax, hKcontained⟩ :=
        (R.approx n).hammock_closed u (.vertex v) heligN
      exact ⟨K, hKmax, hKcontained.trans (R.approx_subset_closedSet n)⟩

/-- Construct the countable moving-stage sequence inside the fixed global
reservoir.  The final interval row is deliberately absent from every input
and conclusion of this theorem. -/
theorem exists_of_reservoir
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ seed : Set V)
    (H : Ladder.Stage (succ kappa) → Set V)
    (hGlobalRoof : globalZ ⊆ C.ladder.limitRoof)
    (hGlobalHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      globalZ globalZ C.ladder.limitStrictRoof C.ladder.limitRoof kappa)
    (hGlobalReferenceClosed :
      ClosedUnderPaths Gamma C.ladder.limitWarp globalZ)
    (hseedGlobal : seed ⊆ globalZ)
    (hseedCard : #seed ≤ kappa)
    (hHcard : ∀ a ∈ C.club, C.newStage < a → #(H a) ≤ kappa)
    (hHglobal : ∀ a ∈ C.club, C.newStage < a → H a ⊆ globalZ) :
    Nonempty (MovingBetaOmegaClosure C globalZ seed H) := by
  classical
  let firstExists := StableDynamic931Closure.exists_of_seed_above
    C globalZ seed C.newStage hGlobalRoof hGlobalHammocks
      hGlobalReferenceClosed hseedGlobal hseedCard
  let first : StableDynamic931Closure C globalZ :=
    Classical.choose firstExists
  have hfirst : seed ⊆ first.closedSet :=
    (Classical.choose_spec firstExists).1
  let nextExists (S : StableDynamic931Closure C globalZ) :=
    StableDynamic931Closure.exists_successor C globalZ H hGlobalRoof
      hGlobalHammocks hGlobalReferenceClosed hHcard hHglobal S
  let next (S : StableDynamic931Closure C globalZ) :
      StableDynamic931Closure C globalZ :=
    Classical.choose (nextExists S)
  have hnext (S : StableDynamic931Closure C globalZ) :
      S.closedSet ⊆ (next S).closedSet ∧
      H S.stage ⊆ (next S).closedSet ∧ S.stage < (next S).stage :=
    Classical.choose_spec (nextExists S)
  let approx : ℕ → StableDynamic931Closure C globalZ :=
    fun n => Nat.rec first (fun _ S => next S) n
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

/-- Concrete specialization to the source's symmetric-difference carrier
`H_beta`.  The sole additional reservoir input is precisely the earlier
paper invariant saying these carriers were recorded in `globalZ`. -/
theorem exists_for_movingReferenceDifference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ seed : Set V)
    (hGlobalRoof : globalZ ⊆ C.ladder.limitRoof)
    (hGlobalHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      globalZ globalZ C.ladder.limitStrictRoof C.ladder.limitRoof kappa)
    (hGlobalReferenceClosed :
      ClosedUnderPaths Gamma C.ladder.limitWarp globalZ)
    (hseedGlobal : seed ⊆ globalZ)
    (hseedCard : #seed ≤ kappa)
    (hDifferenceGlobal : ∀ b ∈ C.club, C.newStage < b →
      C.movingReferenceDifference C.newStage b ⊆ globalZ) :
    Nonempty (MovingBetaOmegaClosure C globalZ seed
      (fun b => C.movingReferenceDifference C.newStage b)) := by
  apply exists_of_reservoir C globalZ seed
    (fun b => C.movingReferenceDifference C.newStage b)
    hGlobalRoof hGlobalHammocks hGlobalReferenceClosed hseedGlobal hseedCard
  · intro b hb hcurrent
    exact C.mk_movingReferenceDifference_le hcurrent.le C.new_mem_club hb
  · exact hDifferenceGlobal

#print axioms StableDynamic931Closure.exists_of_seed_above
#print axioms StableDynamic931Closure.exists_successor
#print axioms MovingBetaOmegaClosure.exists_of_reservoir
#print axioms MovingBetaOmegaClosure.exists_for_movingReferenceDifference
#print axioms MovingBetaOmegaClosure.closedSet_hammock_closed

end MovingBetaOmegaClosure

end Erdos599.Blueprint.LinkageBlueprint
