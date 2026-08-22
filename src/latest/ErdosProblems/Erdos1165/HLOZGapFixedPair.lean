/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZGapMeshEscape

/-!
# A literal fixed creation-pair certificate for HLOZ Lemma 4.10

The finite HLOZ decomposition records the old and new creation times in its
band index.  At such a fixed pair the old clock is a deterministic stopping
time, the deficit inequality gives all required candidate visits before the
new creation time, and the absence of a level-`m+1` site at the terminal
fourth creation forbids any intervening visit to the old favorite.

This file packages those literal facts as the guarded sharp-return witness.
-/

open MeasureTheory ProbabilityTheory Set

namespace Erdos1165.HLOZGapFixedPair

open HLOZGapEstimate HLOZGapStoppedCandidate HLOZGapPointReturn
open HLOZGapGuardedPointReturn HLOZGapMeshEscape HLOZPathEvents

noncomputable section

/-- The point occupying a fixed slot of a path-dependent candidate set.  The
zero fallback is irrelevant on the associated slot-success event. -/
def slotCandidatePoint {Band : Type*}
    (sites : WalkPath → Band → Finset Point) (band : Band) (slot : ℕ)
    (w : StepPath) : Point :=
  (finsetSlot (sites (trajectory w) band) slot).getD 0

lemma slotCandidatePoint_eq_of_slot
    {Band : Type*} {sites : WalkPath → Band → Finset Point}
    {band : Band} {slot : ℕ} {w : StepPath} {x : Point}
    (hslot : finsetSlot (sites (trajectory w) band) slot = some x) :
    slotCandidatePoint sites band slot w = x := by
  simp [slotCandidatePoint, hslot]

/-- Literal data retained from one failed successive-creation pair. -/
def FixedPairRealizes (m oldRank newRank nOld nNew nTerminal : ℕ)
    (a : GapScale) (s : WalkPath) (_band : Unit) (x : Point) : Prop :=
  ThresholdCreation s m oldRank nOld ∧
    ThresholdCreation s m newRank nNew ∧
    thresholdCount s nTerminal (m + 1) = 0 ∧
    nNew ≤ nTerminal ∧
    gapScaleOf m (s nOld) (s nNew) = a ∧
    gapDeficitFailure s m nOld nNew ∧
    x = s nNew

/-- A fixed creation pair together with the return count assigned by its
deficit band.  The final inequality is exactly the deterministic fact needed
to turn the level-`m` creation of `x` into `returns + 1` strict visits after
the old creation time. -/
def FixedPairReturnRealizes
    (m oldRank newRank nOld nNew nTerminal returns : ℕ)
    (a : GapScale) (s : WalkPath) (band : Unit) (x : Point) : Prop :=
  FixedPairRealizes m oldRank newRank nOld nNew nTerminal a s band x ∧
    localTime s nOld x + (returns + 1) ≤ m

/-- The stopped spatial cell used by the guarded point-return iteration. -/
def fixedPairSpatialGuard (m nOld : ℕ) (a : GapScale)
    (candidate : StepPath → Point) : Set StepPath :=
  {w | gapScaleOf m (trajectory w nOld) (candidate w) = a}

/-- An event measurable in the deterministic filtration at time `n` is
observable at the constant stopping time `n`. -/
theorem isMeasurableAtStopping_const_of_measurableSet
    {A : Set StepPath} {n : ℕ}
    (hA : MeasurableSet[incrementFiltration n] A) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n) A := by
  intro q
  by_cases hq : q = n
  · subst q
    have heq : A ∩ {w : StepPath | n = n} = A := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_true]
    rw [heq]
    exact hA
  · have heq : A ∩ {w : StepPath | n = q} = ∅ := by
      ext w
      change (_ ∧ n = q) ↔ False
      constructor
      · rintro ⟨_hw, hnq⟩
        exact (hq hnq.symm).elim
      · exact False.elim
    rw [heq]
    exact (incrementFiltration q).measurableSet_empty

/-- The fixed-pair spatial guard is observable at the old creation time. -/
theorem fixedPairSpatialGuard_observable
    {m nOld : ℕ} {a : GapScale} {candidate : StepPath → Point}
    (hcandidate : ∀ x, IsMeasurableAtStopping (fun _ : StepPath ↦ nOld)
      {w | candidate w = x}) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ nOld)
      (fixedPairSpatialGuard m nOld a candidate) := by
  have hold : ∀ x, IsMeasurableAtStopping (fun _ : StepPath ↦ nOld)
      {w | trajectory w nOld = x} := by
    intro x
    simpa only [stoppedLocation] using
      (stoppedLocation_fiber_observable
        (isFiniteStoppingTime_const nOld) x)
  simpa only [fixedPairSpatialGuard] using
    (isMeasurableAtStopping_binary_fiber hold hcandidate
      (fun x y ↦ gapScaleOf m x y) a)

/-- One literal failed creation pair produces the complete guarded sharp
return witness.  No probabilistic input occurs here. -/
noncomputable def guardedFixedPairSlotWitness
    {Band : Type*} (sites : WalkPath → Band → Finset Point)
    (band : Band) (slot : ℕ)
    (m oldRank newRank nOld nNew nTerminal : ℕ) (a : GapScale)
    (ha : a ∈ properGapMesh)
    (holdRank : 0 < oldRank) (hnewRank : 0 < newRank)
    (hrank : oldRank < newRank)
    (hOldNew : nOld < nNew)
    (hcandidate : ∀ x, IsMeasurableAtStopping (fun _ : StepPath ↦ nOld)
      {w | slotCandidatePoint sites band slot w = x}) :
    GuardedStoppedCandidatePointReturnWitness
      (slotSuccessEvent sites
        (fun s (_band : Band) x ↦
          FixedPairRealizes m oldRank newRank nOld nNew nTerminal a s () x)
        band slot)
      (nNew + 1) (gapDeficitCutoff m a) (meshPointEscapeChance m a) where
  base := {
    candidateWitness := {
      past := fun _ ↦ nOld
      candidate := slotCandidatePoint sites band slot
      past_isStopping := isFiniteStoppingTime_const nOld
      past_lt_deadline := fun _ ↦ hOldNew.trans (Nat.lt_succ_self nNew)
      candidate_observable := hcandidate
      event_gain := by
        intro w hw
        obtain ⟨x, hslot, hrealizes⟩ := hw
        have hcandidateEq : slotCandidatePoint sites band slot w = x :=
          slotCandidatePoint_eq_of_slot hslot
        have hx : x = trajectory w nNew := hrealizes.2.2.2.2.2.2
        have hgain := gapDeficitFailure_localTime_gain hnewRank
          hrealizes.2.1 hrealizes.2.2.2.2.2.1 (Nat.lt_succ_self nNew)
        rw [hrealizes.2.2.2.2.1] at hgain
        simpa only [hcandidateEq, hx, Nat.succ_sub_one] using hgain }
    oldFavorite := fun w ↦ trajectory w nOld
    oldFavorite_observable := by
      intro x
      simpa only [stoppedLocation] using
        (stoppedLocation_fiber_observable
          (isFiniteStoppingTime_const nOld) x)
    event_distinct := by
      intro w hw
      obtain ⟨x, hslot, hrealizes⟩ := hw
      have hcandidateEq : slotCandidatePoint sites band slot w = x :=
        slotCandidatePoint_eq_of_slot hslot
      have hx : x = trajectory w nNew := hrealizes.2.2.2.2.2.2
      change trajectory w nOld ≠ slotCandidatePoint sites band slot w
      rw [hcandidateEq, hx]
      exact creation_locations_ne holdRank hnewRank hrank
        hrealizes.1 hrealizes.2.1
    event_no_old_visit := by
      intro w hw q hOldQ hq
      obtain ⟨_x, _hslot, hrealizes⟩ := hw
      have havoid := no_oldCreation_visit_of_no_next_level holdRank
        hrealizes.1 hrealizes.2.2.1
      exact havoid q hOldQ
        ((Nat.lt_succ_iff.mp hq).trans hrealizes.2.2.2.1) }
  guard := fixedPairSpatialGuard m nOld a
    (slotCandidatePoint sites band slot)
  guard_observable := fixedPairSpatialGuard_observable hcandidate
  event_guard := by
    intro w hw
    obtain ⟨x, hslot, hrealizes⟩ := hw
    have hcandidateEq : slotCandidatePoint sites band slot w = x :=
      slotCandidatePoint_eq_of_slot hslot
    have hx : x = trajectory w nNew := hrealizes.2.2.2.2.2.2
    change gapScaleOf m (trajectory w nOld)
      (slotCandidatePoint sites band slot w) = a
    rw [hcandidateEq, hx]
    exact hrealizes.2.2.2.2.1
  guard_lower := by
    intro w hguard hdistinct
    exact meshPointEscapeChance_le_pointBeforeReturnProbability ha hguard
      hdistinct

/-- Beta-band version of `guardedFixedPairSlotWitness`.  Its return count is
an arbitrary deterministic lower bound certified by the realization event,
so it applies directly to every Proposition 4.8 deficit band. -/
noncomputable def guardedFixedPairReturnSlotWitness
    {Band : Type*} (sites : WalkPath → Band → Finset Point)
    (band : Band) (slot : ℕ)
    (m oldRank newRank nOld nNew nTerminal returns : ℕ) (a : GapScale)
    (ha : a ∈ properGapMesh)
    (holdRank : 0 < oldRank) (hnewRank : 0 < newRank)
    (hrank : oldRank < newRank)
    (hOldNew : nOld < nNew)
    (hcandidate : ∀ x, IsMeasurableAtStopping (fun _ : StepPath ↦ nOld)
      {w | slotCandidatePoint sites band slot w = x}) :
    GuardedStoppedCandidatePointReturnWitness
      (slotSuccessEvent sites
        (fun s (_band : Band) x ↦
          FixedPairReturnRealizes m oldRank newRank nOld nNew nTerminal
            returns a s () x)
        band slot)
      (nNew + 1) returns (meshPointEscapeChance m a) where
  base := {
    candidateWitness := {
      past := fun _ ↦ nOld
      candidate := slotCandidatePoint sites band slot
      past_isStopping := isFiniteStoppingTime_const nOld
      past_lt_deadline := fun _ ↦ hOldNew.trans (Nat.lt_succ_self nNew)
      candidate_observable := hcandidate
      event_gain := by
        intro w hw
        obtain ⟨x, hslot, hrealizes, hreturn⟩ := hw
        have hcandidateEq : slotCandidatePoint sites band slot w = x :=
          slotCandidatePoint_eq_of_slot hslot
        have hx : x = trajectory w nNew := hrealizes.2.2.2.2.2.2
        have hthreshold : m ≤ localTime (trajectory w) nNew x := by
          rw [hx]
          exact (mem_thresholdSites (trajectory w) nNew m
            (trajectory w nNew)).mp
              (position_mem_thresholdSites_of_creation hnewRank
                hrealizes.2.1) |>.2
        rw [Nat.add_sub_cancel, hcandidateEq]
        exact hreturn.trans hthreshold }
    oldFavorite := fun w ↦ trajectory w nOld
    oldFavorite_observable := by
      intro x
      simpa only [stoppedLocation] using
        (stoppedLocation_fiber_observable
          (isFiniteStoppingTime_const nOld) x)
    event_distinct := by
      intro w hw
      obtain ⟨x, hslot, hrealizes, _hreturn⟩ := hw
      have hcandidateEq : slotCandidatePoint sites band slot w = x :=
        slotCandidatePoint_eq_of_slot hslot
      have hx : x = trajectory w nNew := hrealizes.2.2.2.2.2.2
      change trajectory w nOld ≠ slotCandidatePoint sites band slot w
      rw [hcandidateEq, hx]
      exact creation_locations_ne holdRank hnewRank hrank
        hrealizes.1 hrealizes.2.1
    event_no_old_visit := by
      intro w hw q hOldQ hq
      obtain ⟨_x, _hslot, hrealizes, _hreturn⟩ := hw
      have havoid := no_oldCreation_visit_of_no_next_level holdRank
        hrealizes.1 hrealizes.2.2.1
      exact havoid q hOldQ
        ((Nat.lt_succ_iff.mp hq).trans hrealizes.2.2.2.1) }
  guard := fixedPairSpatialGuard m nOld a
    (slotCandidatePoint sites band slot)
  guard_observable := fixedPairSpatialGuard_observable hcandidate
  event_guard := by
    intro w hw
    obtain ⟨x, hslot, hrealizes, _hreturn⟩ := hw
    have hcandidateEq : slotCandidatePoint sites band slot w = x :=
      slotCandidatePoint_eq_of_slot hslot
    have hx : x = trajectory w nNew := hrealizes.2.2.2.2.2.2
    change gapScaleOf m (trajectory w nOld)
      (slotCandidatePoint sites band slot w) = a
    rw [hcandidateEq, hx]
    exact hrealizes.2.2.2.2.1
  guard_lower := by
    intro w hguard hdistinct
    exact meshPointEscapeChance_le_pointBeforeReturnProbability ha hguard
      hdistinct

end

end Erdos1165.HLOZGapFixedPair
