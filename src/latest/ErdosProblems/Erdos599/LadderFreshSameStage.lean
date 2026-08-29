/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderSplitProvenance

/-!
# Isolating the genuinely fresh same-stage hanging branch

Split provenance makes the obstruction exact.  Every hanging stage either
has a strictly earlier marker origin, to which the usual injective-regressive
argument applies, or its selected path is genuinely new and begins at the
marker born at that same stage.  The final theorem in this file is the sound
replacement for arguments which previously removed all of `phiHanging`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Hanging stages whose selected record has a strictly earlier marker
origin. -/
def strictHangingStages (L : G.KappaLadder kappa) :
    Set (Ladder.Stage kappa) :=
  {a | ∃ p : G.DPath, a ∈ L.phiHanging ∧
    L.chosen a = some p ∧
      ∃ b : Ladder.Stage kappa,
        b < a ∧ L.marker b = some p.initial}

/-- The genuine same-stage remainder: the selected path was not current and
starts at the marker inserted at its own record stage. -/
def freshSameStageHangingStages (L : G.KappaLadder kappa) :
    Set (Ladder.Stage kappa) :=
  {a | ∃ p : G.DPath, a ∈ L.phiHanging ∧
    L.chosen a = some p ∧
      p ∉ G.inessentialPaths (L.warpAt a) ∧
        L.marker a = some p.initial}

/-- Version of the cover with bookkeeping validity supplied explicitly.
This is the form used by the legality interface below. -/
theorem phiHanging_subset_strictHanging_union_freshSameStage_of_valid
    (L : G.KappaLadder kappa) (hvalid : L.HasValidBookkeeping)
    (hL : L.HasSplitHangingProvenance) :
    L.phiHanging ⊆ L.strictHangingStages ∪
      L.freshSameStageHangingStages := by
  intro a ha
  let p : G.DPath := L.selectedPath hvalid ⟨a, ha.1⟩
  have hp : L.chosen a = some p :=
    L.chosen_selectedPath hvalid ⟨a, ha.1⟩
  rcases hL.resolve a ha p hp with hstrict | hsame
  · exact Or.inl ⟨p, ha, hp, hstrict⟩
  · exact Or.inr ⟨p, ha, hp, hsame⟩

/-- Same-stage hanging records are members of the existing genuinely fresh
record set used by the grounding development. -/
theorem freshSameStageHangingStages_subset_freshInessentialRecordStages
    (L : G.KappaLadder kappa) :
    L.freshSameStageHangingStages ⊆ L.freshInessentialRecordStages := by
  rintro a ⟨p, ha, hp, hpNotCurrent, _hmarker⟩
  refine ⟨ha.1, ?_⟩
  rintro ⟨q, hq, hqCurrent⟩
  have hqp : q = p := Option.some.inj (hq.symm.trans hp)
  exact hpNotCurrent (hqp ▸ hqCurrent)

theorem strictHangingStages_subset_phi (L : G.KappaLadder kappa) :
    L.strictHangingStages ⊆ L.phi := by
  rintro a ⟨p, ha, _hp, _hprior⟩
  exact ha.1

/-- Strict provenance for the selected path at a strict hanging stage. -/
private theorem strictHangingStage_selectedProvenance
    (L : G.KappaLadder kappa) (hvalid : L.HasValidBookkeeping)
    {a : Ladder.Stage kappa} (ha : a ∈ L.strictHangingStages) :
    ∃ b : Ladder.Stage kappa, b < a ∧
      L.marker b = some
        (L.selectedPath hvalid ⟨a, L.strictHangingStages_subset_phi ha⟩).initial := by
  obtain ⟨p, haHanging, hp, b, hba, hb⟩ := ha
  have hpSelected := L.chosen_selectedPath hvalid ⟨a, haHanging.1⟩
  have hpeq : p = L.selectedPath hvalid ⟨a, haHanging.1⟩ :=
    Option.some.inj (hp.symm.trans hpSelected)
  exact ⟨b, hba, by simpa [hpeq] using hb⟩

/-- The strictly earlier origin at a strict hanging stage. -/
noncomputable def strictHangingOrigin (L : G.KappaLadder kappa)
    (hvalid : L.HasValidBookkeeping) (a : Ladder.Stage kappa) :
    Ladder.Stage kappa := by
  classical
  exact if ha : a ∈ L.strictHangingStages then
    Classical.choose (L.strictHangingStage_selectedProvenance hvalid ha)
  else a

theorem strictHangingOrigin_spec (L : G.KappaLadder kappa)
    (hvalid : L.HasValidBookkeeping) {a : Ladder.Stage kappa}
    (ha : a ∈ L.strictHangingStages) :
    L.strictHangingOrigin hvalid a < a ∧
      L.marker (L.strictHangingOrigin hvalid a) =
        some (L.selectedPath hvalid
          ⟨a, L.strictHangingStages_subset_phi ha⟩).initial := by
  rw [strictHangingOrigin, dif_pos ha]
  exact Classical.choose_spec
    (L.strictHangingStage_selectedProvenance hvalid ha)

theorem strictHangingOrigin_regressive (L : G.KappaLadder kappa)
    (hvalid : L.HasValidBookkeeping) :
    Stationary.IsRegressiveOn L.strictHangingStages
      (L.strictHangingOrigin hvalid) :=
  fun _ ha ↦ (L.strictHangingOrigin_spec hvalid ha).1

/-- Persistence and warp disjointness make the strict origin injective. -/
theorem strictHangingOrigin_injOn (L : G.KappaLadder kappa)
    (hvalid : L.HasValidBookkeeping)
    (hwarp : L.HasWarpStages)
    (hpersist : L.RecordedPathsPersist) :
    Set.InjOn (L.strictHangingOrigin hvalid) L.strictHangingStages := by
  intro a ha b hb hab
  let pa : G.DPath :=
    L.selectedPath hvalid ⟨a, L.strictHangingStages_subset_phi ha⟩
  let pb : G.DPath :=
    L.selectedPath hvalid ⟨b, L.strictHangingStages_subset_phi hb⟩
  have hpa : L.chosen a = some pa :=
    L.chosen_selectedPath hvalid
      ⟨a, L.strictHangingStages_subset_phi ha⟩
  have hpb : L.chosen b = some pb :=
    L.chosen_selectedPath hvalid
      ⟨b, L.strictHangingStages_subset_phi hb⟩
  have hinitial : pa.initial = pb.initial := by
    have hma := (L.strictHangingOrigin_spec hvalid ha).2
    have hmb := (L.strictHangingOrigin_spec hvalid hb).2
    rw [hab] at hma
    exact Option.some.inj (hma.symm.trans hmb)
  rcases lt_trichotomy a b with hablt | rfl | hbalt
  · have hpaIE : pa ∈ G.inessentialPaths (L.successorWarp b) := by
      apply hpersist a pa hpa (Ladder.Stage.succExtended b)
      change a.1 + 1 ≤ b.1 + 1
      rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
      exact Order.succ_le_succ hablt.le
    have hpaWarp : pa ∈ L.successorWarp b := hpaIE.1
    have hpbWarp : pb ∈ L.successorWarp b :=
      (L.bookkeeping.chosen_mem_available hvalid hpb).1.1
    by_cases hp : pa = pb
    · exact L.bookkeeping.chosen_stage_unique hvalid hpa (hp ▸ hpb)
    · exact False.elim <| Set.disjoint_left.1
        (hwarp (Ladder.Stage.succExtended b) hpaWarp hpbWarp hp)
        pa.initial_mem_support (hinitial ▸ pb.initial_mem_support)
  · rfl
  · have hpbIE : pb ∈ G.inessentialPaths (L.successorWarp a) := by
      apply hpersist b pb hpb (Ladder.Stage.succExtended a)
      change b.1 + 1 ≤ a.1 + 1
      rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
      exact Order.succ_le_succ hbalt.le
    have hpbWarp : pb ∈ L.successorWarp a := hpbIE.1
    have hpaWarp : pa ∈ L.successorWarp a :=
      (L.bookkeeping.chosen_mem_available hvalid hpa).1.1
    by_cases hp : pa = pb
    · exact L.bookkeeping.chosen_stage_unique hvalid hpa (hp ▸ hpb)
    · exact False.elim <| Set.disjoint_left.1
        (hwarp (Ladder.Stage.succExtended a) hpaWarp hpbWarp hp)
        pa.initial_mem_support (hinitial ▸ pb.initial_mem_support)

theorem strictHangingStages_not_stationary (L : G.KappaLadder kappa)
    (hL : L.SplitLegalityInvariant) :
    ¬ Stationary.IsStationaryBelow kappa L.strictHangingStages :=
  Stationary.not_isStationaryBelow_of_injOn_regressive
    hL.uncountable hL.regular
    (L.strictHangingOrigin_regressive hL.validBookkeeping)
    (L.strictHangingOrigin_injOn hL.validBookkeeping
      hL.warpStages hL.recordedPathsPersist)

/-- Drop-in stationary-set replacement for the legacy step which removed
all hanging stages.  Under sound split legality, a stationary set of
obstruction indices has either a stationary grounded part or a stationary
genuinely fresh same-stage hanging part. -/
theorem stationary_ground_or_freshSameStageHanging
    (L : G.KappaLadder kappa) (hL : L.SplitLegalityInvariant)
    (E : Set (Ladder.Stage kappa))
    (hE : Stationary.IsStationaryBelow kappa E)
    (hEphi : E ⊆ L.phi) :
    Stationary.IsStationaryBelow kappa (E ∩ L.phiGround) ∨
      Stationary.IsStationaryBelow kappa
        (E ∩ L.freshSameStageHangingStages) := by
  let U := (E ∩ L.phiGround) ∪
    (E ∩ L.freshSameStageHangingStages)
  have hcover : E ⊆ U ∪ L.strictHangingStages := by
    intro a ha
    by_cases hground : a ∈ L.phiGround
    · exact Or.inl (Or.inl ⟨ha, hground⟩)
    · have hhanging : a ∈ L.phiHanging := ⟨hEphi ha, hground⟩
      rcases L.phiHanging_subset_strictHanging_union_freshSameStage_of_valid
          hL.validBookkeeping hL.splitHangingProvenance hhanging with
          hstrict | hsame
      · exact Or.inr hstrict
      · exact Or.inl (Or.inr ⟨ha, hsame⟩)
  have hUorStrict : Stationary.IsStationaryBelow kappa
      (U ∪ L.strictHangingStages) := hE.mono hcover
  have hcof : Order.cof (Ladder.Stage kappa) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift hL.regular]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hL.uncountable).ne'
  have hU : Stationary.IsStationaryBelow kappa U :=
    (isStationary_union_iff hcof).mp hUorStrict |>.resolve_right
      (L.strictHangingStages_not_stationary hL)
  exact (isStationary_union_iff hcof).mp hU

end KappaLadder
end DWeb
end Erdos599
