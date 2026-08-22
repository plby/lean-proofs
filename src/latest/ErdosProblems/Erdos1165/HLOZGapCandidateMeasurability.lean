/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZGapCandidateRealization
import ErdosProblems.Erdos1165.HLOZProposition48Candidates

/-!
# Prefix measurability of the Proposition 4.8 candidate slots

At a deterministic old creation time, every ingredient of the stopped
candidate set is a statistic of the finite increment prefix.  This file
packages that fact in a form which does not require unfolding the arbitrary
post-prefix extension used by the stopped disintegration.
-/

open MeasureTheory ProbabilityTheory Set

namespace Erdos1165.HLOZGapCandidateMeasurability

open ExternalThickCount HLOZGapEstimate HLOZGapFixedPair
open HLOZPathEvents HLOZProposition48Candidates LazyDecomposition
open NearFavoriteShells PreStoppingSpatialLaw ScreeningInstantiation
open StoppedInsertion

noncomputable section

/-- Proposition 4.8's candidate Finset evaluated directly on a finite
increment prefix. -/
noncomputable def prefixCandidateSites48 (o : Orientation) {n : ℕ}
    (externalThreshold : ℕ)
    (distinguished : (Fin n → Direction) → Finset Point)
    (totalLocalTime : (Fin n → Direction) → Point → ℕ)
    (m : ℕ) (beta : ℝ) (u : Fin n → Direction) : Finset Point := by
  classical
  exact boundedCandidates
    ((orientedExternalPath o (trajectoryPrefix u)).toFinset.filter
      (orientationClass o) |>.filter fun x ↦
        externalThreshold ≤
            listLocalTime (orientedExternalPath o (trajectoryPrefix u)) x ∧
          x ∉ distinguished u)
    (fun x ↦ (m - totalLocalTime u x) / shellWidth48 m)
    (shellCount48 m beta)

/-- The same candidate statistic on a finite position prefix. -/
noncomputable def walkPrefixCandidateSites48 (o : Orientation) {n : ℕ}
    (externalThreshold : ℕ)
    (distinguished : (Fin (n + 1) → Point) → Finset Point)
    (totalLocalTime : (Fin (n + 1) → Point) → Point → ℕ)
    (m : ℕ) (beta : ℝ) (u : Fin (n + 1) → Point) : Finset Point := by
  classical
  exact boundedCandidates
    ((orientedExternalPath o u).toFinset.filter (orientationClass o) |>.filter
      fun x ↦ externalThreshold ≤ listLocalTime (orientedExternalPath o u) x ∧
        x ∉ distinguished u)
    (fun x ↦ (m - totalLocalTime u x) / shellWidth48 m)
    (shellCount48 m beta)

/-- Walk-path measurability of the stopped candidate set, stated with the
literal finite-prefix factorization used by all concrete local-time
profiles. -/
theorem measurable_stoppedCandidateSites48
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ)
    (distinguishedPrefix : (Fin (n + 1) → Point) → Finset Point)
    (totalLocalTimePrefix : (Fin (n + 1) → Point) → Point → ℕ)
    (hdistinguished : ∀ s,
      distinguished s = distinguishedPrefix (pathPrefix s n))
    (htotal : ∀ s x,
      totalLocalTime s x = totalLocalTimePrefix (pathPrefix s n) x) :
    Measurable (fun s : WalkPath ↦ stoppedCandidateSites48 o n
      externalThreshold distinguished totalLocalTime m beta s) := by
  have hprefix : Measurable
      (walkPrefixCandidateSites48 o externalThreshold distinguishedPrefix
        totalLocalTimePrefix m beta ∘ (fun s ↦ pathPrefix s n)) :=
    (measurable_of_countable
      (walkPrefixCandidateSites48 o externalThreshold distinguishedPrefix
        totalLocalTimePrefix m beta)).comp (measurable_pathPrefix n)
  convert hprefix using 1
  funext s
  unfold stoppedCandidateSites48 externalThickCandidates deficitShellLabel
    walkPrefixCandidateSites48 orientedExternalVisitedSites
    orientedExternalLocalTime
  simp only [Function.comp_apply]
  rw [hdistinguished]
  congr 2
  funext x
  rw [htotal]

/-- If the distinguished set and stopped total-local-time profile factor
through the first `n` increments, then the concrete candidate Finset is
measurable in the increment filtration at `n`. -/
theorem measurable_stoppedCandidateSites48_trajectory
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ)
    (distinguishedPrefix : (Fin n → Direction) → Finset Point)
    (totalLocalTimePrefix : (Fin n → Direction) → Point → ℕ)
    (hdistinguished : ∀ w,
      distinguished (trajectory w) = distinguishedPrefix (stepPrefix n w))
    (htotal : ∀ w x,
      totalLocalTime (trajectory w) x =
        totalLocalTimePrefix (stepPrefix n w) x) :
    Measurable[incrementFiltration n]
      (fun w : StepPath ↦ stoppedCandidateSites48 o n externalThreshold
        distinguished totalLocalTime m beta (trajectory w)) := by
  rw [incrementFiltration_apply]
  change Measurable[MeasurableSpace.comap (stepPrefix n) MeasurableSpace.pi]
    (fun w : StepPath ↦ stoppedCandidateSites48 o n externalThreshold
      distinguished totalLocalTime m beta (trajectory w))
  have hprefix : Measurable[MeasurableSpace.comap (stepPrefix n)
      MeasurableSpace.pi]
      (prefixCandidateSites48 o externalThreshold distinguishedPrefix
        totalLocalTimePrefix m beta ∘ stepPrefix n) :=
    (measurable_of_countable
      (prefixCandidateSites48 o externalThreshold distinguishedPrefix
        totalLocalTimePrefix m beta)).comp
      (comap_measurable (stepPrefix n))
  convert hprefix using 1
  funext w
  unfold stoppedCandidateSites48 externalThickCandidates deficitShellLabel
    prefixCandidateSites48 orientedExternalVisitedSites
    orientedExternalLocalTime
  simp only [Function.comp_apply]
  rw [trajectoryPrefix_stepPrefix, hdistinguished]
  congr 2
  funext x
  rw [htotal]

/-- Every deterministic slot of a prefix-measurable candidate Finset is a
stopped-past observable point (with the standard zero fallback). -/
theorem slotCandidatePoint_observable_of_prefix
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ)
    (distinguishedPrefix : (Fin n → Direction) → Finset Point)
    (totalLocalTimePrefix : (Fin n → Direction) → Point → ℕ)
    (hdistinguished : ∀ w,
      distinguished (trajectory w) = distinguishedPrefix (stepPrefix n w))
    (htotal : ∀ w x,
      totalLocalTime (trajectory w) x =
        totalLocalTimePrefix (stepPrefix n w) x)
    (slot : ℕ) (x : Point) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      {w | slotCandidatePoint
        (fun s (_ : Unit) ↦ stoppedCandidateSites48 o n externalThreshold
          distinguished totalLocalTime m beta s)
        () slot w = x} := by
  apply isMeasurableAtStopping_const_of_measurableSet
  have hsites := measurable_stoppedCandidateSites48_trajectory o n
    externalThreshold distinguished totalLocalTime m beta
    distinguishedPrefix totalLocalTimePrefix hdistinguished htotal
  have hpoint : Measurable[incrementFiltration n]
      (fun w : StepPath ↦
        (finsetSlot
          (stoppedCandidateSites48 o n externalThreshold distinguished
            totalLocalTime m beta (trajectory w)) slot).getD 0) :=
    (measurable_of_countable
      (fun S : Finset Point ↦ (finsetSlot S slot).getD 0)).comp hsites
  exact measurableSet_eq_fun hpoint measurable_const

/-- A fixed-site local time is a finite-prefix measurable statistic. -/
theorem measurable_localTime_fixed (n : ℕ) (x : Point) :
    Measurable fun s : WalkPath ↦ localTime s n x := by
  change Measurable
    ((fun u : Fin (n + 1) → Point ↦ localTimePrefix u x) ∘
      (fun s ↦ pathPrefix s n))
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

/-- The literal fixed-pair beta-return realization predicate is measurable. -/
theorem measurableSet_fixedPairReturnRealizes
    (m oldRank newRank nOld nNew nTerminal returns : ℕ)
    (a : GapScale) (x : Point) :
    MeasurableSet {s : WalkPath |
      FixedPairReturnRealizes m oldRank newRank nOld nNew nTerminal
        returns a s () x} := by
  have hold := measurableSet_thresholdCreationSet m oldRank nOld
  have hnew := measurableSet_thresholdCreationSet m newRank nNew
  have hterminal : MeasurableSet
      {s : WalkPath | thresholdCount s nTerminal (m + 1) = 0} :=
    measurableSet_eq_fun
      (measurable_thresholdCount nTerminal (m + 1)) measurable_const
  have htime : MeasurableSet {s : WalkPath | nNew ≤ nTerminal} := by
    by_cases h : nNew ≤ nTerminal
    · have heq : {s : WalkPath | nNew ≤ nTerminal} = Set.univ := by
        ext s
        simp [h]
      rw [heq]
      exact MeasurableSet.univ
    · have heq : {s : WalkPath | nNew ≤ nTerminal} = ∅ := by
        ext s
        simp [h]
      rw [heq]
      exact MeasurableSet.empty
  have hscale : MeasurableSet
      {s : WalkPath | gapScaleOf m (s nOld) (s nNew) = a} :=
    measurableSet_pathPairPredicate nOld nNew fun y z ↦
      gapScaleOf m y z = a
  have hfailure := measurableSet_gapDeficitFailure m nOld nNew
  have hx : MeasurableSet {s : WalkPath | x = s nNew} :=
    measurableSet_eq_fun measurable_const (measurable_pi_apply nNew)
  have hreturn : MeasurableSet
      {s : WalkPath | localTime s nOld x + (returns + 1) ≤ m} := by
    exact (measurable_localTime_fixed nOld x)
      (Set.to_countable {q : ℕ | q + (returns + 1) ≤ m}).measurableSet
  have hbase : MeasurableSet {s : WalkPath |
      FixedPairRealizes m oldRank newRank nOld nNew nTerminal a s () x} := by
    have hall := hold.inter (hnew.inter (hterminal.inter (htime.inter
      (hscale.inter (hfailure.inter hx)))))
    convert hall using 1
    ext s
    simp only [FixedPairRealizes, thresholdCreationSet, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
  have hall := hbase.inter hreturn
  convert hall using 1
  ext s
  simp only [FixedPairReturnRealizes, Set.mem_inter_iff,
    Set.mem_ofPred_eq]

/-- Every slot-success event for a fixed beta-return creation pair is
measurable once the candidate set is given by a finite-prefix statistic. -/
theorem measurableSet_fixedPairReturn_slotSuccessEvent
    (o : Orientation) (n externalThreshold : ℕ)
    (distinguished : WalkPath → Finset Point)
    (totalLocalTime : WalkPath → Point → ℕ)
    (m : ℕ) (beta : ℝ)
    (distinguishedPrefix : (Fin (n + 1) → Point) → Finset Point)
    (totalLocalTimePrefix : (Fin (n + 1) → Point) → Point → ℕ)
    (hdistinguished : ∀ s,
      distinguished s = distinguishedPrefix (pathPrefix s n))
    (htotal : ∀ s x,
      totalLocalTime s x = totalLocalTimePrefix (pathPrefix s n) x)
    (oldRank newRank nOld nNew nTerminal returns : ℕ)
    (a : GapScale) (slot : ℕ) :
    MeasurableSet
      (slotSuccessEvent
        (fun s (_ : Unit) ↦ stoppedCandidateSites48 o n externalThreshold
          distinguished totalLocalTime m beta s)
        (fun s (_ : Unit) x ↦
          FixedPairReturnRealizes m oldRank newRank nOld nNew nTerminal
            returns a s () x)
        () slot) := by
  let sites : WalkPath → Finset Point := fun s ↦
    stoppedCandidateSites48 o n externalThreshold distinguished
      totalLocalTime m beta s
  have hsites : Measurable sites := measurable_stoppedCandidateSites48 o n
    externalThreshold distinguished totalLocalTime m beta distinguishedPrefix
    totalLocalTimePrefix hdistinguished htotal
  have hslot (x : Point) : MeasurableSet
      {s : WalkPath | finsetSlot (sites s) slot = some x} := by
    exact hsites (Set.to_countable
      {S : Finset Point | finsetSlot S slot = some x}).measurableSet
  have heq : slotSuccessEvent (fun s (_ : Unit) ↦ sites s)
      (fun s (_ : Unit) x ↦
        FixedPairReturnRealizes m oldRank newRank nOld nNew nTerminal
          returns a s () x) () slot =
      ⋃ x : Point, {s | finsetSlot (sites s) slot = some x} ∩
        {s | FixedPairReturnRealizes m oldRank newRank nOld nNew nTerminal
          returns a s () x} := by
    ext s
    simp only [slotSuccessEvent, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff]
  rw [heq]
  exact MeasurableSet.iUnion fun x ↦
    (hslot x).inter (measurableSet_fixedPairReturnRealizes m oldRank newRank
      nOld nNew nTerminal returns a x)

/-! ## Canonical old-prefix data -/

/-- Favorite-domino bases evaluated directly on a position prefix. -/
noncomputable def favoriteDominoBasesPrefix (o : Orientation) {n : ℕ}
    (u : Fin (n + 1) → Point) : Finset Point :=
  (favoritePrefix u).image (dominoBase o)

lemma favoriteDominoBases_eq_prefix (o : Orientation) (s : WalkPath)
    (n : ℕ) :
    favoriteDominoBases o s n =
      favoriteDominoBasesPrefix o (pathPrefix s n) := by
  rfl

lemma localTime_eq_prefix (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s n x = localTimePrefix (pathPrefix s n) x := by
  rfl

/-- The actual Proposition 4.8 candidate family at the old prefix is
measurable, with no abstract factorization premises. -/
theorem measurable_canonicalStoppedCandidateSites48
    (o : Orientation) (n externalThreshold m : ℕ) (beta : ℝ) :
    Measurable fun s : WalkPath ↦
      stoppedCandidateSites48 o n externalThreshold
        (fun s ↦ favoriteDominoBases o s n)
        (fun s x ↦ localTime s n x) m beta s := by
  exact measurable_stoppedCandidateSites48 o n externalThreshold
    (fun s ↦ favoriteDominoBases o s n) (fun s x ↦ localTime s n x)
    m beta (favoriteDominoBasesPrefix o) localTimePrefix
    (favoriteDominoBases_eq_prefix o · n) (localTime_eq_prefix · n)

/-- Every slot of the canonical old-prefix candidate family is observable
at that deterministic old time. -/
theorem canonicalSlotCandidatePoint_observable
    (o : Orientation) (n externalThreshold m : ℕ) (beta : ℝ)
    (slot : ℕ) (x : Point) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      {w | slotCandidatePoint
        (fun s (_ : Unit) ↦ stoppedCandidateSites48 o n externalThreshold
          (fun s ↦ favoriteDominoBases o s n)
          (fun s x ↦ localTime s n x) m beta s)
        () slot w = x} := by
  exact slotCandidatePoint_observable_of_prefix o n externalThreshold
    (fun s ↦ favoriteDominoBases o s n) (fun s x ↦ localTime s n x)
    m beta
    (fun u ↦ favoriteDominoBasesPrefix o (trajectoryPrefix u))
    (fun u x ↦ localTimePrefix (trajectoryPrefix u) x)
    (fun w ↦ by rw [favoriteDominoBases_eq_prefix,
      trajectoryPrefix_stepPrefix])
    (fun w x ↦ by rw [localTime_eq_prefix, trajectoryPrefix_stepPrefix])
    slot x

/-- Canonical fixed-pair slot-success measurability. -/
theorem measurableSet_canonicalFixedPairReturn_slotSuccessEvent
    (o : Orientation) (n externalThreshold m : ℕ) (beta : ℝ)
    (oldRank newRank nOld nNew nTerminal returns : ℕ)
    (a : GapScale) (slot : ℕ) :
    MeasurableSet
      (slotSuccessEvent
        (fun s (_ : Unit) ↦ stoppedCandidateSites48 o n externalThreshold
          (fun s ↦ favoriteDominoBases o s n)
          (fun s x ↦ localTime s n x) m beta s)
        (fun s (_ : Unit) x ↦
          FixedPairReturnRealizes m oldRank newRank nOld nNew nTerminal
            returns a s () x)
        () slot) := by
  exact measurableSet_fixedPairReturn_slotSuccessEvent o n externalThreshold
    (fun s ↦ favoriteDominoBases o s n) (fun s x ↦ localTime s n x)
    m beta (favoriteDominoBasesPrefix o) localTimePrefix
    (favoriteDominoBases_eq_prefix o · n) (localTime_eq_prefix · n)
    oldRank newRank nOld nNew nTerminal returns a slot

end

end Erdos1165.HLOZGapCandidateMeasurability
