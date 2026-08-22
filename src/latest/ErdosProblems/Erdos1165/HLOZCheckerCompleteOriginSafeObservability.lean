/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCheckerOriginSafeDistinguishedProp49Family
import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationScreenObservability

/-!
# Stopped observability of the complete checker Proposition 4.9 family

The complete target family treats the shifted origin either as an exposed
coordinate or as a distinguished coordinate.  Both branches are built from
the same prefixed all-creation stopped cylinders.  Hence their union remains
observable on a fixed creation atom.  Pulling it through the fixed checker
first step then gives the rank-one stopped-past input required by the mesh
constructor.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCheckerCompleteOriginSafeObservability

open HLOZCheckerOriginSafeDistinguishedProp49Family
open HLOZCheckerOriginSafeProp49Family
open HLOZCheckerPrefixedCylinderTransport
open FiniteDominoProductLaw
open HLOZFilteredOrientedAllCreationStoppedCandidateFamily
open HLOZMeshCandidatePolynomialNumerics
open HLOZNoLazyMeshCandidateCreation
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents
open HLOZPrefixedAllCreationScreenObservability
open HLOZPrefixedAllCreationCanonicalRefinement
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49Observability
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSpatialAdapter
open HLOZStoppedHistoryCandidateFuture
open HLOZThetaOneSourceShift
open HLOZTypedStoppedCandidateObservability
open LazyDecomposition PreStoppingFiber StoppedInsertion
open SpatialInsertionFiber
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem screen_mem_atom
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (fiber : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (cap : ℕ)
    (predicate : TilingCappedCoordinates z.external.retainedCount
      (fiber.coordinateCap cap) → Prop)
    (hpredicate : ∀ q, predicate q → fiber.atomPredicate cap q)
    {s : WalkPath}
    (hs : s ∈ allCreationScreenFiber fiber cap predicate) :
    s ∈ orientedAllCreationSupportTraceAtom t o m k supportAt z S := by
  apply fiber.atom_sound cap
  exact ⟨hs.1, prefixedTilingPreStoppingFiberEvent_mono
    (fiber.stoppingTime cap) (fiber.initial cap) t (fiber.start cap)
    (fiber.retained cap) (fiber.tail cap) hpredicate hs.2⟩

private theorem sourceOriginSafeNear_preimage_iff_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    {omega omega' : StepPath}
    (hp : stepPrefix n omega = stepPrefix n omega')
    (hcreation : ThresholdCreation (trajectory omega) m k n)
    (hcreation' : ThresholdCreation (trajectory omega') m k n) :
    trajectory omega ∈ sourceOriginSafeNear eta a candidate hcandidate low e
        horigin ↔
      trajectory omega' ∈ sourceOriginSafeNear eta a candidate hcandidate low e
        horigin := by
  constructor
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨cap, hcap⟩
    refine Set.mem_iUnion.mpr ⟨cap, ?_⟩
    exact (allCreationScreenFiber_preimage_iff_of_stepPrefix_eq
      (SourceFiber eta) cap
      (sourceOriginSafeScreenedPredicate eta a candidate hcandidate low e
        horigin cap) rfl hp hcreation hcreation').mp hcap
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨cap, hcap⟩
    refine Set.mem_iUnion.mpr ⟨cap, ?_⟩
    exact (allCreationScreenFiber_preimage_iff_of_stepPrefix_eq
      (SourceFiber eta) cap
      (sourceOriginSafeScreenedPredicate eta a candidate hcandidate low e
        horigin cap) rfl hp hcreation hcreation').mpr hcap

private theorem sourceDistinguishedOriginSafeNear_preimage_iff_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {omega omega' : StepPath}
    (hp : stepPrefix n omega = stepPrefix n omega')
    (hcreation : ThresholdCreation (trajectory omega) m k n)
    (hcreation' : ThresholdCreation (trajectory omega') m k n) :
    trajectory omega ∈ sourceDistinguishedOriginSafeNear eta a candidate
        hcandidate low good e hm hk hwindow harithmetic hexternalArithmetic ↔
      trajectory omega' ∈ sourceDistinguishedOriginSafeNear eta a candidate
        hcandidate low good e hm hk hwindow harithmetic hexternalArithmetic := by
  constructor
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨cap, hcap⟩
    refine Set.mem_iUnion.mpr ⟨cap, ?_⟩
    exact (allCreationScreenFiber_preimage_iff_of_stepPrefix_eq
      (SourceFiber eta) cap
      (sourceDistinguishedOriginSafeScreenedPredicate eta a candidate
        hcandidate low good e hm hk hwindow harithmetic hexternalArithmetic cap)
      rfl hp hcreation hcreation').mp hcap
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨cap, hcap⟩
    refine Set.mem_iUnion.mpr ⟨cap, ?_⟩
    exact (allCreationScreenFiber_preimage_iff_of_stepPrefix_eq
      (SourceFiber eta) cap
      (sourceDistinguishedOriginSafeScreenedPredicate eta a candidate
        hcandidate low good e hm hk hwindow harithmetic hexternalArithmetic cap)
      rfl hp hcreation hcreation').mpr hcap

private theorem completeOriginSafeCandidateNear_preimage_iff_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (candidate : Point) (heligible : SourceProp49EligibleHistory eta)
    (hcandidate : candidate ∈ eta.1.2)
    {omega omega' : StepPath}
    (hp : stepPrefix n omega = stepPrefix n omega')
    (hcreation : ThresholdCreation (trajectory omega) m k n)
    (hcreation' : ThresholdCreation (trajectory omega') m k n) :
    trajectory omega ∈ completeOriginSafeCandidateNear eta a low e hm hk
        hwindow harithmetic hexternalArithmetic candidate ↔
      trajectory omega' ∈ completeOriginSafeCandidateNear eta a low e hm hk
        hwindow harithmetic hexternalArithmetic candidate := by
  by_cases horigin : targetOriginBase t e ∈ eta.1.2
  · simpa only [completeOriginSafeCandidateNear, heligible, horigin,
      sourceOriginSafeCandidateNear, hcandidate, dite_true] using
      sourceOriginSafeNear_preimage_iff_of_stepPrefix_eq eta a candidate
        hcandidate low e horigin hp hcreation hcreation'
  · let hdistinguished : DistinguishedOriginSafeEligibleHistory e eta :=
      ⟨heligible, horigin⟩
    simpa only [completeOriginSafeCandidateNear, heligible, horigin,
      sourceDistinguishedOriginSafeCandidateNear, hdistinguished, hcandidate,
      dite_true, dite_false] using
      sourceDistinguishedOriginSafeNear_preimage_iff_of_stepPrefix_eq eta a
        candidate hcandidate low heligible.good e hm hk hwindow harithmetic
        hexternalArithmetic hp hcreation hcreation'

private theorem completeOriginSafeCandidateNear_subset_piece
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (candidate : Point) (heligible : SourceProp49EligibleHistory eta)
    (hcandidate : candidate ∈ eta.1.2) :
    completeOriginSafeCandidateNear eta a low e hm hk hwindow harithmetic
        hexternalArithmetic candidate ⊆
      historyPiece t o m k (SourceSupportAt t o m)
        (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta) := by
  intro s hs
  by_cases horigin : targetOriginBase t e ∈ eta.1.2
  · have hnear : s ∈ sourceOriginSafeNear eta a candidate hcandidate low e
        horigin := by
      simpa only [completeOriginSafeCandidateNear, heligible, horigin,
        sourceOriginSafeCandidateNear, hcandidate, dite_true] using hs
    rcases Set.mem_iUnion.mp hnear with ⟨cap, hcap⟩
    have hbase : s ∈ sourceOriginSafeBaseFiber eta a candidate hcandidate low
        e horigin cap := by
      exact ⟨hcap.1, prefixedTilingPreStoppingFiberEvent_mono
        ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        ((SourceFiber eta).tail cap)
        (sourceOriginSafeScreenedPredicate_subset_base eta a candidate
          hcandidate low e horigin cap) hcap.2⟩
    have hprevious := sourceOriginSafeBaseFiber_subset_previous eta a candidate
      hcandidate low e horigin cap hbase
    have hatom : s ∈ orientedAllCreationSupportTraceAtom t o m k
        (SourceSupportAt t o m) eta.1.1 eta.1.2 := by
      apply screen_mem_atom (SourceFiber eta) cap
        (sourceOriginSafeScreenedPredicate eta a candidate hcandidate low e
          horigin cap) (fun _q hq ↦ hq.1)
      exact hcap
    exact ⟨hprevious, hatom⟩
  · let hdistinguished : DistinguishedOriginSafeEligibleHistory e eta :=
      ⟨heligible, horigin⟩
    have hnear : s ∈ sourceDistinguishedOriginSafeNear eta a candidate
        hcandidate low heligible.good e hm hk hwindow harithmetic
          hexternalArithmetic := by
      simpa only [completeOriginSafeCandidateNear, heligible, horigin,
        sourceDistinguishedOriginSafeCandidateNear, hdistinguished, hcandidate,
        dite_true, dite_false] using hs
    rcases Set.mem_iUnion.mp hnear with ⟨cap, hcap⟩
    rw [sourceDistinguishedOriginSafeScreenedFiber_eq eta a candidate
      hcandidate low heligible.good e horigin hm hk hwindow harithmetic
      hexternalArithmetic cap] at hcap
    change s ∈ sourceProp49ScreenedFiber eta a candidate hcandidate low cap ∩
      targetOriginSafe m k e at hcap
    have hcanonicalNear : s ∈ sourceProp49CandidateNear eta a low candidate := by
      simp only [sourceProp49CandidateNear, hcandidate, dite_true]
      exact Set.mem_iUnion.mpr ⟨cap, hcap.1⟩
    have hatom := sourceProp49CandidateNear_subset_atom eta a low candidate
      hcandidate hcanonicalNear
    exact ⟨⟨hcap.2, hatom.1.2.1⟩, hatom⟩

private theorem completeOriginSafeTargetFamily_preimage_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {omega omega' : StepPath}
    (hp : stepPrefix n omega = stepPrefix n omega')
    (hcreation : ThresholdCreation (trajectory omega) m k n)
    (hcreation' : ThresholdCreation (trajectory omega') m k n)
    (hmember : trajectory omega ∈
      (completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk
        hwindow harithmetic hwidth hexternalArithmetic).someCandidate) :
    trajectory omega' ∈
      (completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk
        hwindow harithmetic hwidth hexternalArithmetic).someCandidate := by
  unfold StoppedHistoryCandidateFamily.someCandidate at hmember ⊢
  rcases Set.mem_iUnion.mp hmember with ⟨history, hhistory⟩
  rcases Set.mem_iUnion.mp hhistory with ⟨candidate, hcandidate⟩
  rcases Set.mem_iUnion.mp hcandidate with ⟨hcandidate, _hpiece, hnear⟩
  cases history with
  | none =>
      simp [completeOriginSafeTargetFamily, filteredHistoryCandidates] at hcandidate
  | some eta =>
      have heligible : SourceProp49EligibleHistory eta ∧
          candidate ∈ eta.1.2 := by
        change candidate ∈ filteredHistoryCandidates t o m k
          (SourceSupportAt t o m) SourceProp49EligibleHistory (some eta) at hcandidate
        exact (mem_filteredHistoryCandidates_some_iff t o m k
          (SourceSupportAt t o m) SourceProp49EligibleHistory eta candidate).mp hcandidate
      have hnear' : trajectory omega' ∈
          completeOriginSafeCandidateNear eta a low e hm hk hwindow harithmetic
            hexternalArithmetic candidate :=
        (completeOriginSafeCandidateNear_preimage_iff_of_stepPrefix_eq eta a
          low e hm hk hwindow harithmetic hexternalArithmetic candidate
          heligible.1 heligible.2 hp hcreation hcreation').mp hnear
      have hpiece' := completeOriginSafeCandidateNear_subset_piece eta a low e
        hm hk hwindow harithmetic hexternalArithmetic candidate heligible.1
          heligible.2 hnear'
      exact Set.mem_iUnion.mpr ⟨some eta,
        Set.mem_iUnion.mpr ⟨candidate,
          Set.mem_iUnion.mpr ⟨hcandidate, hpiece', hnear'⟩⟩⟩

/-- The complete origin-safe target candidate union is observable on every
fixed target rank-creation atom. -/
theorem completeOriginSafeTargetFamily_fixedCreation_observable
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      {omega | ThresholdCreation (trajectory omega) m k n ∧
        trajectory omega ∈
          (completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk
            hwindow harithmetic hwidth hexternalArithmetic).someCandidate} := by
  apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
  apply measurableSet_incrementFiltration_of_stepPrefix_dependent n
  intro omega omega' hp
  have hpPath : pathPrefix (trajectory omega) n =
      pathPrefix (trajectory omega') n := by
    simpa only [trajectoryPrefix_stepPrefix] using congrArg trajectoryPrefix hp
  have hcreationIff :=
    TilingDistinguishedTraceInvariant.thresholdCreation_iff_of_pathPrefix_eq
      (m := m) (rank := k) hpPath le_rfl
  constructor
  · rintro ⟨hcreation, hcandidate⟩
    have hcreation' := hcreationIff.mp hcreation
    exact ⟨hcreation', completeOriginSafeTargetFamily_preimage_of_stepPrefix_eq
      a low e hm hk hwindow harithmetic hwidth hexternalArithmetic hp hcreation
        hcreation' hcandidate⟩
  · rintro ⟨hcreation', hcandidate'⟩
    have hcreation := hcreationIff.mpr hcreation'
    exact ⟨hcreation, completeOriginSafeTargetFamily_preimage_of_stepPrefix_eq
      a low e hm hk hwindow harithmetic hwidth hexternalArithmetic hp.symm
        hcreation' hcreation hcandidate'⟩

private theorem someCandidate_subset_previous
    {History Candidate : Type*} [Countable History]
    {previous : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily History Candidate previous budget
      ratio) :
    family.someCandidate ⊆ previous := by
  intro s hs
  unfold StoppedHistoryCandidateFamily.someCandidate at hs
  rcases Set.mem_iUnion.mp hs with ⟨history, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨candidate, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨_hcandidate, hpiece, _hnear⟩
  have hunion : s ∈ ⋃ h, family.piece h := Set.mem_iUnion_of_mem history hpiece
  rw [family.piece_union] at hunion
  exact hunion

private theorem checkerCompleteOriginSafeFamily_preimage_of_stepPrefix_eq
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {omega omega' : StepPath}
    (hp : stepPrefix n omega = stepPrefix n omega')
    (hcreation : ThresholdCreation (trajectory omega) m k n)
    (hcreation' : ThresholdCreation (trajectory omega') m k n)
    (hmember : trajectory omega ∈
      (checkerCompleteOriginSafeFamily (t := t) (o := o) a low e hm hk
        hwindow harithmetic hwidth hexternalArithmetic).someCandidate) :
    trajectory omega' ∈
      (checkerCompleteOriginSafeFamily (t := t) (o := o) a low e hm hk
        hwindow harithmetic hwidth hexternalArithmetic).someCandidate := by
  let family := completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk
    hwindow harithmetic hwidth hexternalArithmetic
  rw [checkerCompleteOriginSafeFamily_someCandidate] at hmember ⊢
  rcases hmember with ⟨hfirst, htarget⟩
  have hprevious : oneStepRecenter (trajectory omega) ∈
      targetOriginSafe m k e ∩ thresholdReachStage m k :=
    someCandidate_subset_previous family htarget
  have hnpos : 0 < n :=
    HLOZThetaOneSourceShift.thresholdCreation_time_pos_of_two_le omega
      (by omega) hk hcreation
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  have hfirstSteps : omega ∈ firstDirectionSteps e :=
    (Set.ext_iff.mp (trajectory_preimage_firstDirectionWalk e) omega).mp hfirst
  have hpzero := congrFun hp (show Fin (N + 1) from ⟨0, by omega⟩)
  have hfirstSteps' : omega' ∈ firstDirectionSteps e := by
    change omega' 0 = e
    change omega 0 = e at hfirstSteps
    exact hpzero.symm.trans hfirstSteps
  have hfirst' : trajectory omega' ∈ firstDirectionWalk e :=
    (Set.ext_iff.mp (trajectory_preimage_firstDirectionWalk e) omega').mpr
      hfirstSteps'
  have htargetReach : ReachesThreshold
      (oneStepRecenter (trajectory omega)) m k := hprevious.2
  have htargetCreationAtClock : ThresholdCreation
      (oneStepRecenter (trajectory omega)) m k
        (creationTimeNat m k (oneStepRecenter (trajectory omega))) := by
    have hfind := thresholdCreation_natFind htargetReach
    simpa only [creationTimeNat, htargetReach, dif_pos] using hfind
  have hsafeAtClock : localTime (oneStepRecenter (trajectory omega))
        (creationTimeNat m k (oneStepRecenter (trajectory omega)))
        (0 - trajectory omega 1) + 1 < m := by
    have hsafe := hprevious.1
    change localTime (oneStepRecenter (trajectory omega))
        (creationTimeNat m k (oneStepRecenter (trajectory omega)))
        (0 - directionVector e) + 1 < m at hsafe
    change trajectory omega 1 = directionVector e at hfirst
    rw [hfirst]
    exact hsafe
  have hphysicalFromTarget :=
    thresholdCreation_of_oneStepRecenter_of_originSafe omega hm hk
      htargetCreationAtClock hsafeAtClock
  have hclockEq : creationTimeNat m k (oneStepRecenter (trajectory omega)) = N := by
    have htime := thresholdCreation_time_unique hphysicalFromTarget hcreation
    omega
  have htargetCreation : ThresholdCreation
      (oneStepRecenter (trajectory omega)) m k N := by
    simpa only [hclockEq] using htargetCreationAtClock
  have horiginPhysical : localTime (trajectory omega) (N + 1) 0 < m := by
    rw [← localTime_oneStepRecenter_origin_add_one omega N]
    simpa only [hclockEq] using hsafeAtClock
  have hpPath : pathPrefix (trajectory omega) (N + 1) =
      pathPrefix (trajectory omega') (N + 1) := by
    simpa only [trajectoryPrefix_stepPrefix] using congrArg trajectoryPrefix hp
  have horiginPhysical' : localTime (trajectory omega') (N + 1) 0 < m := by
    rw [← localTime_eq_of_pathPrefix_eq hpPath 0]
    exact horiginPhysical
  have htargetCreation' : ThresholdCreation
      (oneStepRecenter (trajectory omega')) m k N :=
    HLOZThetaOneSourceShift.thresholdCreation_oneStepRecenter omega' N m k
      (by omega) hcreation' horiginPhysical'
  have hpShift : stepPrefix N (shiftSteps 1 omega) =
      stepPrefix N (shiftSteps 1 omega') := by
    funext j
    simpa only [stepPrefix, shiftSteps, Nat.add_comm] using
      congrFun hp ⟨j.1 + 1, by omega⟩
  change oneStepRecenter (trajectory omega) ∈ family.someCandidate at htarget
  rw [oneStepRecenter_trajectory] at htarget htargetCreation
  rw [oneStepRecenter_trajectory] at htargetCreation'
  have htarget' : trajectory (shiftSteps 1 omega') ∈ family.someCandidate :=
    completeOriginSafeTargetFamily_preimage_of_stepPrefix_eq a low e hm hk
      hwindow harithmetic hwidth hexternalArithmetic hpShift htargetCreation
        htargetCreation' htarget
  have htarget'' : oneStepRecenter (trajectory omega') ∈
      family.someCandidate := by
    simpa only [oneStepRecenter_trajectory] using htarget'
  change trajectory omega' ∈ firstDirectionWalk e ∧
    oneStepRecenter (trajectory omega') ∈ family.someCandidate
  exact ⟨hfirst', htarget''⟩

/-- A fixed-direction complete checker candidate row is observable on every
physical rank-creation atom. -/
theorem checkerCompleteOriginSafeFamily_fixedCreation_observable
    {t : DominoTiling} {o : Orientation} {m k n : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      {omega | ThresholdCreation (trajectory omega) m k n ∧
        trajectory omega ∈
          (checkerCompleteOriginSafeFamily (t := t) (o := o) a low e hm hk
            hwindow harithmetic hwidth hexternalArithmetic).someCandidate} := by
  apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
  apply measurableSet_incrementFiltration_of_stepPrefix_dependent n
  intro omega omega' hp
  have hpPath : pathPrefix (trajectory omega) n =
      pathPrefix (trajectory omega') n := by
    simpa only [trajectoryPrefix_stepPrefix] using congrArg trajectoryPrefix hp
  have hcreationIff :=
    TilingDistinguishedTraceInvariant.thresholdCreation_iff_of_pathPrefix_eq
      (m := m) (rank := k) hpPath le_rfl
  constructor
  · rintro ⟨hcreation, hcandidate⟩
    have hcreation' := hcreationIff.mp hcreation
    exact ⟨hcreation', checkerCompleteOriginSafeFamily_preimage_of_stepPrefix_eq
      a low e hm hk hwindow harithmetic hwidth hexternalArithmetic hp hcreation
        hcreation' hcandidate⟩
  · rintro ⟨hcreation', hcandidate'⟩
    have hcreation := hcreationIff.mpr hcreation'
    exact ⟨hcreation, checkerCompleteOriginSafeFamily_preimage_of_stepPrefix_eq
      a low e hm hk hwindow harithmetic hwidth hexternalArithmetic hp.symm
        hcreation' hcreation hcandidate'⟩

/-- Exact rank-one atom form consumed by the raw mesh-creation adapter. -/
theorem checkerCompleteOriginSafeFamily_firstCandidatePastAtom_observable
    {t : DominoTiling} {o : Orientation} {m n : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (trajectory ⁻¹' firstCandidatePastAtom
        (checkerCompleteOriginSafeFamily (t := t) (o := o) (k := 1) a low e hm
          (by omega : 0 < (1 : ℕ)) hwindow harithmetic hwidth
            hexternalArithmetic).someCandidate m n) := by
  change IsMeasurableAtStopping (fun _ : StepPath ↦ n)
    {omega | ThresholdCreation (trajectory omega) m 1 n ∧
      trajectory omega ∈
        (checkerCompleteOriginSafeFamily (t := t) (o := o) (k := 1) a low e hm
          (by omega : 0 < (1 : ℕ)) hwindow harithmetic hwidth
            hexternalArithmetic).someCandidate}
  exact checkerCompleteOriginSafeFamily_fixedCreation_observable
    (t := t) (o := o) (m := m) (k := 1) (n := n) a low e hm
      (by omega : 0 < (1 : ℕ)) hwindow harithmetic hwidth hexternalArithmetic

end

end Erdos1165.HLOZCheckerCompleteOriginSafeObservability
