/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingBetaSequence
import ErdosProblems.Erdos599.HalfwayClubRangeSup
import ErdosProblems.Erdos599.DeferredLimitFrontierBirth
import ErdosProblems.Erdos599.IndexedRelationLimitHitSource

/-!+# The genuine limit of the moving-stage closure

The countable closing sequence has a club supremum strictly above every
chosen stage.  Stable capture at each approximation therefore captures the
entire union at that supremum.  The moving reference difference is also
absorbed: an old hit lost at the supremum was lost at an earlier stage by
hit-stage closure, whereas a new hit at the supremum is witnessed earlier
by finite attainment of its terminal component.

The reservoir and hit-closure hypotheses remain exactly those of the
source construction.  No future interval linkage appears in this proof.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open _root_.Erdos599.DirectedPath Ladder

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

/-- Both halves of the moving reference difference at a genuine limit
already occur along any cofinal earlier family of club stages. -/
theorem movingReferenceDifference_subset_iUnion_at_limit
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure
      Gamma C.ladder C.club)
    {I : Type v} [LinearOrder I] [Nonempty I]
    (index : I → Ladder.Stage (succ kappa)) (hmono : Monotone index)
    {a b : Ladder.Stage (succ kappa)}
    (hbLimit : Order.IsSuccLimit b.1)
    (hindex : ∀ i, index i < b)
    (hLUB : IsLUB (Set.range index) b)
    (hClub : ∀ i, index i ∈ C.club) :
    C.movingReferenceDifference a b ⊆
      ⋃ i, C.movingReferenceDifference a (index i) := by
  classical
  rintro x ⟨p, hp, hxp⟩
  rcases hp with ⟨hpa, hpb⟩ | ⟨hpb, hpa⟩
  · have hsome : ∃ i, p ∉ C.limitReferenceAtFrontier (index i) := by
      by_contra hnot
      have hall : ∀ i, p ∈ C.limitReferenceAtFrontier (index i) := by
        intro i
        by_contra hi
        exact hnot ⟨i, hi⟩
      apply hpb
      refine ⟨hpa.1, ?_⟩
      exact DWeb.KappaLadder.Deferred.limitWarp_meets_frontier_at_iSup
        hHit index hmono hLUB hClub hpa.1 (fun i => (hall i).2)
    obtain ⟨i, hpi⟩ := hsome
    exact Set.mem_iUnion.2 ⟨i, p, Or.inl ⟨hpa, hpi⟩, hxp⟩
  · obtain ⟨i, hpi⟩ :=
      DWeb.KappaLadder.Deferred.path_hit_earlier_of_hit_limit
        C.legal index hbLimit hindex hLUB hpb.2
    exact Set.mem_iUnion.2 ⟨i, p, Or.inr ⟨⟨hpb.1, hpi⟩, hpa⟩, hxp⟩

end ClubStageGeometry

namespace MovingBetaOmegaClosure

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V}
variable {H : Ladder.Stage (succ kappa) → Set V}

/-- The actual monotone sequence of club indices. -/
abbrev stageIndex (R : MovingBetaOmegaClosure C globalZ seed H)
    (n : ℕ) : Ladder.Stage (succ kappa) := (R.approx n).stage

theorem stageIndex_strictMono (R : MovingBetaOmegaClosure C globalZ seed H) :
    StrictMono R.stageIndex :=
  strictMono_nat_of_lt_succ R.stage_strictMono

/-- The supremum of the chosen stages is a genuine limit in the club. -/
theorem exists_limitStage (R : MovingBetaOmegaClosure C globalZ seed H) :
    ∃ a : Ladder.Stage (succ kappa), a ∈ C.club ∧
      IsLUB (Set.range R.stageIndex) a ∧
      (∀ n, R.stageIndex n < a) ∧ Order.IsSuccLimit a.1 := by
  have hNat : Cardinal.lift.{u} #ℕ ≤ Cardinal.lift.{0} kappa := by
    simpa only [Cardinal.mk_nat, Cardinal.lift_aleph0] using
      (Cardinal.lift_le.mpr C.capacity_infinite :
        Cardinal.lift.{0} Cardinal.aleph0 ≤ Cardinal.lift.{0} kappa)
  obtain ⟨D⟩ := HalfwayClubRangeSup.exists_data C.capacity_infinite hNat
    C.club_isClub R.stageIndex R.stageIndex_strictMono.monotone
      (fun n => (R.approx n).stage_mem_club)
  have hstrict : ∀ n, R.stageIndex n < D.supIndex := by
    intro n
    exact (R.stage_strictMono n).trans_le (D.previous_le (n + 1))
  refine ⟨D.supIndex, D.supIndex_mem, D.range_isLUB, hstrict, ?_⟩
  rcases D.attained_or_genuineLimit with ⟨n, hn⟩ | ⟨_, hlim⟩
  · exact False.elim ((hstrict n).ne hn)
  · exact hlim

/-- Tail-stable capture at the approximations captures the full union at
any common upper bound, with exact persistent-frontier intersection. -/
theorem closedSet_captured_at_upper
    (R : MovingBetaOmegaClosure C globalZ seed H)
    {a : Ladder.Stage (succ kappa)} (hupper : ∀ n, R.stageIndex n ≤ a) :
    R.closedSet ⊆ Gamma.roof (C.ladder.frontier a) ∧
    R.closedSet ∩ C.ladder.frontier a = R.closedSet ∩ C.persistent ∧
    R.closedSet \ C.persistent ⊆ Gamma.strictRoof (C.ladder.frontier a) := by
  have hcapture := fun n => (R.approx n).stable_capture a (hupper n)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
    exact (hcapture n).1 hxn
  · ext x
    constructor
    · rintro ⟨hx, hxa⟩
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
      have hxp : x ∈ (R.approx n).closedSet ∩ C.persistent := by
        rw [← (hcapture n).2.1]
        exact ⟨hxn, hxa⟩
      exact ⟨Set.mem_iUnion.2 ⟨n, hxn⟩, hxp.2⟩
    · rintro ⟨hx, hxp⟩
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
      have hxa : x ∈ (R.approx n).closedSet ∩ C.ladder.frontier a := by
        rw [(hcapture n).2.1]
        exact ⟨hxn, hxp⟩
      exact ⟨Set.mem_iUnion.2 ⟨n, hxn⟩, hxa.2⟩
  · rintro x ⟨hx, hxp⟩
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
    exact (hcapture n).2.2 ⟨hxn, hxp⟩

/-- The concrete source difference is absorbed at the supremum, not only
at the previously chosen sequence of stages. -/
theorem movingReferenceDifference_subset_closedSet_at_limit
    (R : MovingBetaOmegaClosure C globalZ seed
      (fun b => C.movingReferenceDifference C.newStage b))
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure
      Gamma C.ladder C.club)
    {a : Ladder.Stage (succ kappa)} (haLimit : Order.IsSuccLimit a.1)
    (hindex : ∀ n, R.stageIndex n < a)
    (hLUB : IsLUB (Set.range R.stageIndex) a) :
    C.movingReferenceDifference C.newStage a ⊆ R.closedSet := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1
    (C.movingReferenceDifference_subset_iUnion_at_limit hHit R.stageIndex
      R.stageIndex_strictMono.monotone haLimit hindex hLUB
        (fun n => (R.approx n).stage_mem_club) hx)
  exact R.carrier_subset_closedSet n hxn

end MovingBetaOmegaClosure

/-- The source-order closure together with its exact limit-frontier and
moving-difference conclusions.  The interval row is still chosen later. -/
structure LimitMoving931GlobalClosure
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ seed : Set V) extends DynamicMoving931GlobalClosure C globalZ seed where
  frontier_inter : closedSet ∩ C.ladder.frontier later.stage =
    closedSet ∩ C.persistent
  nonpersistent_strict : closedSet \ C.persistent ⊆
    Gamma.strictRoof (C.ladder.frontier later.stage)
  difference_subset : C.movingReferenceDifference C.newStage later.stage ⊆ closedSet
  stage_isLimit : Order.IsSuccLimit later.stage.1

namespace MovingBetaOmegaClosure

/-- Finish the moving-stage closing construction at its actual club
supremum.  All additional fields are proved, not supplied as inputs. -/
theorem exists_limitClosure
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ seed : Set V}
    (R : MovingBetaOmegaClosure C globalZ seed
      (fun b => C.movingReferenceDifference C.newStage b))
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure
      Gamma C.ladder C.club) :
    Nonempty (LimitMoving931GlobalClosure C globalZ seed) := by
  obtain ⟨a, haClub, haLUB, hindex, haLimit⟩ := R.exists_limitStage
  have hcapture := R.closedSet_captured_at_upper (fun n => (hindex n).le)
  refine ⟨{
    closedSet := R.closedSet
    seed_subset := R.seed_subset_closedSet
    subset_global := R.closedSet_subset_global
    card_le := R.closedSet_card_le
    hammock_closed := R.closedSet_hammock_closed
    reference_closed := R.closedSet_reference_closed
    subset_limitRoof := R.closedSet_subset_limitRoof
    later := {
      stage := a
      mem_club := haClub
      current_lt := (R.approx 0).current_lt_stage.trans (hindex 0)
      subset_roof := hcapture.1
    }
    frontier_inter := hcapture.2.1
    nonpersistent_strict := hcapture.2.2
    difference_subset :=
      R.movingReferenceDifference_subset_closedSet_at_limit
        hHit haLimit hindex haLUB
    stage_isLimit := haLimit
  }⟩

end MovingBetaOmegaClosure

#print axioms ClubStageGeometry.movingReferenceDifference_subset_iUnion_at_limit
#print axioms MovingBetaOmegaClosure.exists_limitStage
#print axioms MovingBetaOmegaClosure.closedSet_captured_at_upper
#print axioms MovingBetaOmegaClosure.exists_limitClosure

end Erdos599.Blueprint.LinkageBlueprint
