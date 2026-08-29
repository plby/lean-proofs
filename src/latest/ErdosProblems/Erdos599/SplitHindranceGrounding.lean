/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderFreshSameStage
import ErdosProblems.Erdos599.LadderLemma76

/-!
# Grounding reduction for split-legal ladder hindrances

The canonical successor-normalized ladder is `IsSplitLegal`, rather than
legacy `IsLegal`: a record which first becomes inessential at a successor
may start at the marker inserted at that same stage.  This file packages the
stationary obstruction using the sound legality predicate and proves the
exact replacement for legacy `IsKappaHindrance.phiGround_isStationary`.

After the strictly-earlier hanging records are removed by pressing down, a
stationary obstruction has either stationary grounded records or stationary
genuinely fresh same-stage records.  Splitting the grounded alternative at
the current/successor boundary gives the three branches consumed by the
corrected grounding construction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- A stationary obstruction equipped with the sound successor-normalized
legality package.  Unlike legacy `IsKappaHindrance`, this structure does not
assert the false strict provenance law for same-stage records. -/
structure IsSplitKappaHindrance (L : G.KappaLadder kappa) : Prop where
  legal : L.IsSplitLegal
  stationary : Stationary.IsStationaryBelow kappa L.phi

/-- Split legality supplies every construction law used by source Lemma
7.6; the repaired provenance field is irrelevant to that lemma. -/
theorem IsSplitLegal.lemma76Data {L : G.KappaLadder kappa}
    (hL : L.IsSplitLegal) : L.Lemma76Data where
  waveRungs := hL.waveRungs
  exactSuccessorArrows := hL.exactSuccessorArrows
  roofsSourceAtStages := hL.roofsSourceAtStages
  recordedPathsPersist := hL.recordedPathsPersist

/-- Lemma 7.6 for a successor-normalized split-legal ladder. -/
theorem IsSplitLegal.phiHindrance_subset_phi
    {L : G.KappaLadder kappa} (hL : L.IsSplitLegal)
    (hG : G.IsNormalized) : L.phiHindrance ⊆ L.phi :=
  L.phiHindrance_subset_phi_of_lemma76Data hG hL.lemma76Data

/-- Every grounded record is an obstruction record. -/
theorem phiGround_subset_phi (L : G.KappaLadder kappa)
    (hvalid : L.HasValidBookkeeping) :
    L.phiGround ⊆ L.phi := by
  rintro a ⟨p, hp, _hpSource⟩
  exact (L.bookkeeping.mem_phi_iff_exists_chosen hvalid).2 ⟨p, hp⟩

/-- Same-stage hanging records are obstruction records. -/
theorem freshSameStageHangingStages_subset_phi
    (L : G.KappaLadder kappa) :
    L.freshSameStageHangingStages ⊆ L.phi := by
  rintro a ⟨p, ha, _hp, _hpFresh, _hmarker⟩
  exact ha.1

/-- Sound replacement for legacy `IsKappaHindrance.phiGround_isStationary`.
The second disjunct is the real equal-index case introduced by successor
normalization, and therefore cannot be discarded locally. -/
theorem IsSplitKappaHindrance.phiGround_or_freshSameStage_isStationary
    (L : G.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    Stationary.IsStationaryBelow kappa L.phiGround ∨
      Stationary.IsStationaryBelow kappa
        L.freshSameStageHangingStages := by
  rcases L.stationary_ground_or_freshSameStageHanging
      hL.legal.splitLegalityInvariant L.phi hL.stationary
      (fun _ ha ↦ ha) with hground | hfresh
  · left
    simpa only [Set.inter_eq_right.2
      (L.phiGround_subset_phi hL.legal.validBookkeeping)] using hground
  · right
    simpa only [Set.inter_eq_right.2
      L.freshSameStageHangingStages_subset_phi] using hfresh

/-- Exact prior/fresh split of the grounded alternative, retaining the
genuinely fresh same-stage hanging case as a third branch.  This is the
stationary input required by a sound successor-corrected grounding switch. -/
theorem IsSplitKappaHindrance.priorGround_or_freshGround_or_sameStage
    (L : G.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    Stationary.IsStationaryBelow kappa
        L.priorInessentialGroundStages ∨
      Stationary.IsStationaryBelow kappa
          L.freshInessentialGroundStages ∨
        Stationary.IsStationaryBelow kappa
          L.freshSameStageHangingStages := by
  rcases hL.phiGround_or_freshSameStage_isStationary L with
      hground | hsame
  · rw [L.phiGround_eq_priorInessential_union_freshInessential
        hL.legal.validBookkeeping] at hground
    have hcof : Order.cof (Ladder.Stage kappa) ≠ ℵ₀ := by
      rw [Stationary.cof_below_eq_lift hL.legal.regular]
      rw [← Cardinal.lift_aleph0.{u + 1, u}]
      exact (Cardinal.lift_lt.mpr hL.legal.uncountable).ne'
    rcases (isStationary_union_iff hcof).mp hground with hprior | hfresh
    · exact Or.inl hprior
    · exact Or.inr (Or.inl hfresh)
  · exact Or.inr (Or.inr hsame)

/-- Eliminate the corrected grounding trichotomy into an ordinary
hindrance.  This is the exact proposition-level handoff between the split
ladder reduction and the three Section 8 grounding constructions; no branch
is silently discarded. -/
theorem IsSplitKappaHindrance.exists_hindrance_of_groundingBranches
    (L : G.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hprior : Stationary.IsStationaryBelow kappa
        L.priorInessentialGroundStages →
      ∃ W : Set G.DPath, G.IsHindrance W)
    (hfresh : Stationary.IsStationaryBelow kappa
        L.freshInessentialGroundStages →
      ∃ W : Set G.DPath, G.IsHindrance W)
    (hsame : Stationary.IsStationaryBelow kappa
        L.freshSameStageHangingStages →
      ∃ W : Set G.DPath, G.IsHindrance W) :
    ∃ W : Set G.DPath, G.IsHindrance W := by
  rcases hL.priorGround_or_freshGround_or_sameStage L with
      hpriorStationary | hfreshStationary | hsameStationary
  · exact hprior hpriorStationary
  · exact hfresh hfreshStationary
  · exact hsame hsameStationary

/-- The actual canonical ladder therefore admits the corrected stationary
grounding trichotomy whenever its obstruction set is stationary. -/
theorem canonicalLadder_priorGround_or_freshGround_or_sameStage
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : ℵ₀ < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hstationary : Stationary.IsStationaryBelow kappa
      (canonicalLadder G kappa preferred).phi) :
    let L := canonicalLadder G kappa preferred
    Stationary.IsStationaryBelow kappa
        L.priorInessentialGroundStages ∨
      Stationary.IsStationaryBelow kappa
          L.freshInessentialGroundStages ∨
        Stationary.IsStationaryBelow kappa
          L.freshSameStageHangingStages := by
  dsimp only
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  exact (IsSplitKappaHindrance.mk hlegal hstationary)
    |>.priorGround_or_freshGround_or_sameStage L

end KappaLadder
end DWeb
end Erdos599
