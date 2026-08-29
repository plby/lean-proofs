/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingFreshRung
import ErdosProblems.Erdos599.FamilyTools

/-!
# Finite avoidance for fresh grounded records

The diagonal augmentation in Section 8 fixes one finite ambient path and
then chooses a fresh grounded record disjoint from it.  This is legitimate
because recorded components persist into the limiting warp: distinct stages
therefore give pairwise vertex-disjoint components, and only finitely many of
them can meet a fixed finite set.

The results here retain the stage indices.  Thus deleting all records meeting
one finite support from a stationary set of fresh grounded stages still leaves
a stationary set, rather than merely producing a single avoiding record.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The record selected at a fresh grounded stage. -/
noncomputable def freshGroundRecordPath
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (a : L.freshInessentialGroundStages) : Gamma.DPath :=
  L.selectedPath hlegal.validBookkeeping ⟨a.1, a.2.2.1⟩

@[simp]
theorem chosen_freshGroundRecordPath
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (a : L.freshInessentialGroundStages) :
    L.chosen a.1 = some (L.freshGroundRecordPath hlegal a) :=
  L.chosen_selectedPath hlegal.validBookkeeping ⟨a.1, a.2.2.1⟩

/-- Every fresh grounded record persists as an inessential component of the
limiting warp. -/
theorem freshGroundRecordPath_mem_limitWarp
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (a : L.freshInessentialGroundStages) :
    L.freshGroundRecordPath hlegal a ∈ L.limitWarp := by
  exact (L.recorded_mem_inessential hlegal.recordedPathsPersist
    (L.chosen_freshGroundRecordPath hlegal a)
    (by
      change a.1.1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 a.1.2)).1

/-- Different fresh grounded stages select different limiting-warp
components. -/
theorem freshGroundRecordPath_injective
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal) :
    Function.Injective (L.freshGroundRecordPath hlegal) := by
  intro a b hab
  apply Subtype.ext
  exact L.bookkeeping.chosen_stage_unique hlegal.validBookkeeping
    (L.chosen_freshGroundRecordPath hlegal a)
    (hab ▸ L.chosen_freshGroundRecordPath hlegal b)

/-- Fresh grounded record components have pairwise-disjoint supports. -/
theorem freshGroundRecordPath_support_pairwiseDisjoint
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal) :
    (Set.univ : Set L.freshInessentialGroundStages).PairwiseDisjoint
      (fun a ↦ (L.freshGroundRecordPath hlegal a).support) := by
  intro a _ha b _hb hab
  exact hlegal.warpStages (Ladder.finalStage kappa)
    (L.freshGroundRecordPath_mem_limitWarp hlegal a)
    (L.freshGroundRecordPath_mem_limitWarp hlegal b)
    (fun hpq ↦ hab (L.freshGroundRecordPath_injective hlegal hpq))

/-- Fresh grounded records which meet a prescribed vertex set. -/
def freshGroundRecordsMeeting
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (S : Set V) : Set L.freshInessentialGroundStages :=
  {a | ((L.freshGroundRecordPath hlegal a).support ∩ S).Nonempty}

/-- Only finitely many fresh grounded record components meet a fixed finite
vertex set. -/
theorem freshGroundRecordsMeeting_finite
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {S : Set V} (hS : S.Finite) :
    (L.freshGroundRecordsMeeting hlegal S).Finite := by
  let pick : L.freshGroundRecordsMeeting hlegal S → S := fun a ↦
    ⟨Classical.choose a.2,
      (Classical.choose_spec a.2).2⟩
  have hpickSupport : ∀ a : L.freshGroundRecordsMeeting hlegal S,
      (pick a : V) ∈ (L.freshGroundRecordPath hlegal a.1).support := by
    intro a
    exact (Classical.choose_spec a.2).1
  have hpickInjective : Function.Injective pick := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have hdisj := L.freshGroundRecordPath_support_pairwiseDisjoint hlegal
      (Set.mem_univ a.1) (Set.mem_univ b.1) hne
    exact Set.disjoint_left.1 hdisj
      (hpickSupport a) (show (pick a : V) ∈
        (L.freshGroundRecordPath hlegal b.1).support by
          rw [hab]
          exact hpickSupport b)
  letI : Finite S := hS.to_subtype
  letI : Finite (L.freshGroundRecordsMeeting hlegal S) :=
    Finite.of_injective pick hpickInjective
  exact Set.toFinite _

/-- Stage-valued version of `freshGroundRecordsMeeting`. -/
def freshGroundStagesMeeting
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (S : Set V) : Set (Ladder.Stage kappa) :=
  Subtype.val '' L.freshGroundRecordsMeeting hlegal S

theorem freshGroundStagesMeeting_finite
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {S : Set V} (hS : S.Finite) :
    (L.freshGroundStagesMeeting hlegal S).Finite :=
  (L.freshGroundRecordsMeeting_finite hlegal hS).image Subtype.val

theorem mem_freshGroundStagesMeeting_iff
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {S : Set V} {a : Ladder.Stage kappa} :
    a ∈ L.freshGroundStagesMeeting hlegal S ↔
      ∃ ha : a ∈ L.freshInessentialGroundStages,
        ((L.freshGroundRecordPath hlegal ⟨a, ha⟩).support ∩ S).Nonempty := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.2, hb⟩
  · rintro ⟨ha, hmeet⟩
    exact ⟨⟨a, ha⟩, hmeet, rfl⟩

/-- Deleting all fresh records meeting a finite set preserves stationarity. -/
theorem freshGround_diff_meeting_isStationary
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (hfresh : Stationary.IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    {S : Set V} (hS : S.Finite) :
    Stationary.IsStationaryBelow kappa
      (L.freshInessentialGroundStages \
        L.freshGroundStagesMeeting hlegal S) := by
  apply PopularSwitching.stationary_diff_of_stationary_of_nonstationary
    hlegal.regular hlegal.uncountable hfresh
  exact Stationary.not_isStationaryBelow_of_countable
    hlegal.regular hlegal.uncountable
    (L.freshGroundStagesMeeting_finite hlegal hS).countable

/-- Every retained record in the stationary finite-avoidance thinning is
vertex-disjoint from the forbidden finite set. -/
theorem freshGroundRecordPath_disjoint_of_mem_diff_meeting
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {S : Set V} {a : Ladder.Stage kappa}
    (ha : a ∈ L.freshInessentialGroundStages \
      L.freshGroundStagesMeeting hlegal S) :
    Disjoint
      (L.freshGroundRecordPath hlegal ⟨a, ha.1⟩).support S := by
  rw [Set.disjoint_left]
  intro x hxp hxS
  apply ha.2
  rw [L.mem_freshGroundStagesMeeting_iff hlegal]
  exact ⟨ha.1, ⟨x, hxp, hxS⟩⟩

/-- Finite-path specialization used by the diagonal augmentation. -/
theorem freshGround_diff_pathSupport_isStationary
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (hfresh : Stationary.IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (R : FinitePath Gamma.graph) :
    Stationary.IsStationaryBelow kappa
      (L.freshInessentialGroundStages \
        L.freshGroundStagesMeeting hlegal R.support) :=
  L.freshGround_diff_meeting_isStationary hlegal hfresh R.support_finite

/-- Above every prescribed stage there is a fresh grounded record avoiding
the fixed finite set.  This is the choice form used when adjoining one more
diagonal route to a previously constructed family. -/
theorem exists_freshGroundRecordPath_gt_disjoint
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (hfresh : Stationary.IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    {S : Set V} (hS : S.Finite) (b : Ladder.Stage kappa) :
    ∃ (a : Ladder.Stage kappa)
        (ha : a ∈ L.freshInessentialGroundStages),
      b < a ∧ Disjoint
        (L.freshGroundRecordPath hlegal ⟨a, ha⟩).support S := by
  have hstat := L.freshGround_diff_meeting_isStationary
    hlegal hfresh hS
  have hlim : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hlegal.regular.aleph0_le
  let b' : Ladder.Stage kappa := ⟨succ b.1, hlim.succ_lt b.2⟩
  obtain ⟨a, ha, hb'a⟩ :=
    Stationary.isCofinal_of_isStationary hstat b'
  refine ⟨a, ha.1, ?_, ?_⟩
  · exact (lt_succ b.1).trans_le hb'a
  · exact L.freshGroundRecordPath_disjoint_of_mem_diff_meeting
      hlegal ha

/-- Finite-path specialization of the strict-above avoiding choice. -/
theorem exists_freshGroundRecordPath_gt_disjoint_path
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (hfresh : Stationary.IsStationaryBelow kappa
      L.freshInessentialGroundStages)
    (R : FinitePath Gamma.graph) (b : Ladder.Stage kappa) :
    ∃ (a : Ladder.Stage kappa)
        (ha : a ∈ L.freshInessentialGroundStages),
      b < a ∧ Disjoint
        (L.freshGroundRecordPath hlegal ⟨a, ha⟩).support R.support :=
  L.exists_freshGroundRecordPath_gt_disjoint
    hlegal hfresh R.support_finite b

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.freshGround_diff_pathSupport_isStationary
#print axioms Erdos599.DWeb.KappaLadder.exists_freshGroundRecordPath_gt_disjoint_path
