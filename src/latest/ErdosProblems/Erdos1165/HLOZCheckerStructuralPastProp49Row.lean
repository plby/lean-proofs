/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCheckerOriginSafeDistinguishedProp49Family
import ErdosProblems.Erdos1165.HLOZCheckerOriginSafeEventProp49Family
import ErdosProblems.Erdos1165.HLOZTransportedStructuralPastProp49Row
import ErdosProblems.Erdos1165.TilingValidTraceCappedStageAdapter

/-!
# Checker structural-past Proposition 4.9 rows

The checker origin-safe candidate screen is narrower than the ordinary
canonical source screen.  This lets its already established raw coverage
enter the structural-past family after one-step recentering.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCheckerStructuralPastProp49Row

open HLOZCheckerOriginSafeDistinguishedProp49Family
open HLOZCheckerOriginSafeEventProp49Family
open HLOZCheckerOriginSafeProp49Family
open HLOZCheckerPrefixedCylinderTransport
open HLOZFilteredOrientedAllCreationStoppedCandidateFamily
open HLOZMeshCandidatePolynomialNumerics
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents
open HLOZPrefixedAllCreationCanonicalDominantWindows
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceDistinguishedEventProp49Family
open HLOZSourceStructuralPastInvariant
open HLOZSourceStructuralPastProp49Family
open HLOZSourceEndpointTransportTable
open HLOZStoppedHistoryCandidateFuture
open HLOZThetaOneSourceShift
open HLOZStructuralPastTransport
open HLOZTransportedCanonicalProp49Row
open HLOZTransportedStructuralPastProp49Row
open LazyDecomposition PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple

theorem sourceOriginSafeScreenedFiber_subset_sourceProp49ScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2)
    (cap : ℕ) :
    sourceOriginSafeScreenedFiber eta a candidate hcandidate low e horigin
        cap ⊆
      sourceProp49ScreenedFiber eta a candidate hcandidate low cap := by
  intro s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  rcases q.2.1 with ⟨hatom, ell, hell, htotal⟩
  refine ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q.1, ?_, q.2.2⟩, hq⟩⟩
  refine ⟨hatom, ell, ?_, htotal⟩
  simp only [originSafeScreenedAccepts,
    PrefixedCanonicalDominantCandidateWindowSpec.acceptedScreenedAccepts,
    decide_eq_true_eq] at hell ⊢
  exact hell.1

theorem sourceOriginSafeNear_subset_sourceProp49Near
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (e : Direction) (horigin : targetOriginBase t e ∈ eta.1.2) :
    sourceOriginSafeNear eta a candidate hcandidate low e horigin ⊆
      sourceProp49Near eta a candidate hcandidate low := by
  intro s hs
  rcases Set.mem_iUnion.mp hs with ⟨cap, hcap⟩
  exact Set.mem_iUnion_of_mem cap
    (sourceOriginSafeScreenedFiber_subset_sourceProp49ScreenedFiber eta a
      candidate hcandidate low e horigin cap hcap)

theorem sourceDistinguishedOriginSafeNear_subset_sourceProp49Near
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (horigin : targetOriginBase t e ∉ eta.1.2)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    sourceDistinguishedOriginSafeNear eta a candidate hcandidate low good e
        hm hk hwindow harithmetic hexternalArithmetic ⊆
      sourceProp49Near eta a candidate hcandidate low := by
  intro s hs
  rcases Set.mem_iUnion.mp hs with ⟨cap, hcap⟩
  rw [sourceDistinguishedOriginSafeScreenedFiber_eq eta a candidate hcandidate
    low good e horigin hm hk hwindow harithmetic hexternalArithmetic cap] at hcap
  exact Set.mem_iUnion_of_mem cap hcap.1

/-- The complete origin-safe target candidate event is contained in the
ordinary unrestricted canonical candidate event. -/
theorem completeOriginSafeTargetFamily_someCandidate_subset_unrestricted
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
        harithmetic hwidth hexternalArithmetic).someCandidate ⊆
      (sourceUnrestrictedTargetFamily t o m k a low hm hk hwindow harithmetic
        hexternalArithmetic).someCandidate := by
  classical
  intro s hs
  unfold StoppedHistoryCandidateFamily.someCandidate at hs ⊢
  rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨candidate, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨hcandidate, hpiece, hnear⟩
  cases h with
  | none =>
      change candidate ∈ (∅ : Finset Point) at hcandidate
      simp at hcandidate
  | some eta =>
      have heligible := (mem_filteredHistoryCandidates_some_iff t o m k
        (SourceSupportAt t o m) SourceProp49EligibleHistory eta candidate).mp
          hcandidate
      have hcandidateEta : candidate ∈ eta.1.2 := heligible.2
      have hordinary : s ∈ sourceProp49CandidateNear eta a low candidate := by
        change s ∈ completeOriginSafeCandidateNear eta a low e hm hk hwindow
          harithmetic hexternalArithmetic candidate at hnear
        by_cases horigin : targetOriginBase t e ∈ eta.1.2
        · simp only [completeOriginSafeCandidateNear, heligible.1, horigin,
            if_pos] at hnear
          change s ∈ sourceOriginSafeCandidateNear eta a low e candidate at hnear
          simp only [sourceOriginSafeCandidateNear, horigin, hcandidateEta,
            dite_true] at hnear
          simp only [sourceProp49CandidateNear, hcandidateEta, dite_true]
          exact sourceOriginSafeNear_subset_sourceProp49Near eta a candidate
            hcandidateEta low e horigin hnear
        · simp only [completeOriginSafeCandidateNear, heligible.1, horigin,
            if_neg] at hnear
          change s ∈ sourceDistinguishedOriginSafeCandidateNear eta a low e
            hm hk hwindow harithmetic hexternalArithmetic candidate at hnear
          have hdistEligible : DistinguishedOriginSafeEligibleHistory e eta :=
            ⟨heligible.1, horigin⟩
          simp only [sourceDistinguishedOriginSafeCandidateNear, hdistEligible,
            hcandidateEta, dite_true] at hnear
          simp only [sourceProp49CandidateNear, hcandidateEta, dite_true]
          exact sourceDistinguishedOriginSafeNear_subset_sourceProp49Near eta a
            candidate hcandidateEta low heligible.1.good e horigin hm hk
            hwindow harithmetic hexternalArithmetic hnear
      refine Set.mem_iUnion_of_mem (some eta) <|
        Set.mem_iUnion_of_mem candidate <|
          Set.mem_iUnion_of_mem hcandidate ?_
      change s ∈ historyPiece t o m k (SourceSupportAt t o m) Set.univ
          (some eta) ∩ sourceProp49CandidateNear eta a low candidate
      exact ⟨⟨Set.mem_univ s, hpiece.2⟩, hordinary⟩

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
  rw [← family.piece_union]
  exact Set.mem_iUnion_of_mem history hpiece

noncomputable def firstCheckerStructuralTargetFamily
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (a : GapScale) (low : ℕ) (e : Direction) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (History (shiftedCheckerTarget d) .even m 2
        (SourceSupportAt (shiftedCheckerTarget d) .even m)) Point
      ((targetOriginSafe m 2 e ∩ thresholdReachStage m 2) ∩
        firstStructuralPast (shiftedCheckerTarget d) m gaps)
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  completeOriginSafeEventTargetFamily a low e
    (firstStructuralPast (shiftedCheckerTarget d) m gaps)
    (measurableSet_firstStructuralPast (shiftedCheckerTarget d) m gaps)
    (fun eta ↦ firstStructuralPast_distinguishedInvariant eta hm gaps)
    (firstStructuralPast_prefixInvariant (shiftedCheckerTarget d) m gaps)
    hm (by omega) hwindow harithmetic hwidth hexternalArithmetic

theorem firstCheckerStructuralTargetFamily_near_measurable
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (a : GapScale) (low : ℕ) (e : Direction) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    ∀ h candidate, MeasurableSet
      ((firstCheckerStructuralTargetFamily d m gaps a low e hm hwindow
        harithmetic hwidth hexternalArithmetic).near h candidate) :=
  completeOriginSafeEventTargetFamily_near_measurable a low e
    (firstStructuralPast (shiftedCheckerTarget d) m gaps)
    (measurableSet_firstStructuralPast (shiftedCheckerTarget d) m gaps)
    (fun eta ↦ firstStructuralPast_distinguishedInvariant eta hm gaps)
    (firstStructuralPast_prefixInvariant (shiftedCheckerTarget d) m gaps)
    hm (by omega) hwindow harithmetic hwidth hexternalArithmetic

noncomputable def firstCheckerStructuralFamily
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (a : GapScale) (low : ℕ) (e : Direction) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :=
  checkerFixedPrefixFamily e
    (firstCheckerStructuralTargetFamily d m gaps a low e hm hwindow harithmetic
      hwidth hexternalArithmetic)
    (firstCheckerStructuralTargetFamily_near_measurable d m gaps a low e hm
      hwindow harithmetic hwidth hexternalArithmetic)

theorem firstCheckerStructuralFamily_someCandidate_subset_complete
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (a : GapScale) (low : ℕ) (e : Direction) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (firstCheckerStructuralFamily d m gaps a low e hm hwindow harithmetic hwidth
        hexternalArithmetic).someCandidate ⊆
      (checkerCompleteOriginSafeFamily
        (t := shiftedCheckerTarget d) (o := .even) (k := 2) a low e hm
          (by omega) hwindow harithmetic hwidth
            hexternalArithmetic).someCandidate := by
  intro s hs
  unfold firstCheckerStructuralFamily at hs
  rw [StoppedHistoryCandidateFamily.someCandidate_checkerFixedPrefixFamily] at hs
  rw [checkerCompleteOriginSafeFamily_someCandidate]
  refine ⟨hs.1, ?_⟩
  exact (completeOriginSafeEventTargetFamily_someCandidate_eq a low e
    (firstStructuralPast (shiftedCheckerTarget d) m gaps)
    (measurableSet_firstStructuralPast (shiftedCheckerTarget d) m gaps)
    (fun eta ↦ firstStructuralPast_distinguishedInvariant eta hm gaps)
    (firstStructuralPast_prefixInvariant (shiftedCheckerTarget d) m gaps)
    hm (by omega) hwindow harithmetic hwidth hexternalArithmetic ▸ hs.2).1

theorem firstCheckerStructuralPrevious_inter_valid_subset
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (e : Direction) (hm : 1 < m) :
    checkerPrefixedPreimage e
      ((targetOriginSafe m 2 e ∩ thresholdReachStage m 2) ∩
        firstStructuralPast (shiftedCheckerTarget d) m gaps) ∩
        validStepWalk ⊆
      firstStructuralPast (.checker d) m gaps := by
  intro s hs
  rcases hs with ⟨⟨hfirst, htarget⟩, hvalid⟩
  rcases htarget with ⟨⟨hsafe, _hreach⟩, hstruct⟩
  let omega := stepsOfWalk s
  have hsTrajectory : trajectory omega = s := hvalid
  have hfirstEq : trajectory omega 1 = directionVector e := by
    rw [hsTrajectory]
    exact hfirst
  rw [← hsTrajectory]
  apply firstStructuralPast_of_oneStepRecenter_of_originSafe omega d e m
    (by omega) gaps hfirstEq
  · simpa only [hsTrajectory] using hsafe
  · simpa only [hsTrajectory, shiftedCheckerTarget, shiftedCheckerTiling]
      using hstruct

theorem firstCheckerStructuralPrevious_measure_le
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (e : Direction) (hm : 1 < m) :
    simpleRandomWalk (checkerPrefixedPreimage e
      ((targetOriginSafe m 2 e ∩ thresholdReachStage m 2) ∩
        firstStructuralPast (shiftedCheckerTarget d) m gaps)) ≤
      simpleRandomWalk (firstStructuralPast (.checker d) m gaps) := by
  let previous := checkerPrefixedPreimage e
    ((targetOriginSafe m 2 e ∩ thresholdReachStage m 2) ∩
      firstStructuralPast (shiftedCheckerTarget d) m gaps)
  have hprevious : MeasurableSet previous :=
    measurableSet_checkerPrefixedPreimage
      (((measurableSet_targetOriginSafe m 2 e).inter
        (measurableSet_thresholdReachStage m 2)).inter
        (measurableSet_firstStructuralPast (shiftedCheckerTarget d) m gaps)) e
  rw [← TilingValidTraceCappedStageAdapter.simpleRandomWalk_inter_validStepWalk
    previous hprevious]
  exact measure_mono
    (firstCheckerStructuralPrevious_inter_valid_subset d m gaps e hm)

theorem checkerComplete_inter_firstStructural_inter_valid_subset
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (a : GapScale) (low : ℕ) (e : Direction) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (checkerCompleteOriginSafeFamily
      (t := shiftedCheckerTarget d) (o := .even) (k := 2) a low e hm
        (by omega)
        hwindow harithmetic hwidth hexternalArithmetic).someCandidate ∩
        firstStructuralPast (.checker d) m gaps ∩ validStepWalk ⊆
      (firstCheckerStructuralFamily d m gaps a low e hm hwindow harithmetic
        hwidth hexternalArithmetic).someCandidate := by
  intro s hs
  rcases hs with ⟨⟨hcomplete, hstruct⟩, hvalid⟩
  rw [checkerCompleteOriginSafeFamily_someCandidate] at hcomplete
  rcases hcomplete with ⟨hfirst, htargetCandidate⟩
  have htargetPrevious := someCandidate_subset_previous
    (completeOriginSafeTargetFamily
      (t := shiftedCheckerTarget d) (o := .even) (k := 2) a low e hm
        (by omega)
        hwindow harithmetic hwidth hexternalArithmetic) htargetCandidate
  have hnotException : s ∈
      (checkerOriginShiftExceptionEvent d m 2 0)ᶜ :=
    checkerPrefixedPreimage_targetOriginSafe_subset_exception_compl d e hm
      (by omega) ⟨⟨hfirst, htargetPrevious⟩, hvalid⟩
  let omega := stepsOfWalk s
  have hsTrajectory : trajectory omega = s := hvalid
  have hfirstEq : trajectory omega 1 = directionVector e := by
    rw [hsTrajectory]
    exact hfirst
  have horigin : localTime (trajectory omega)
      (creationTimeNat m 2 (trajectory omega)) 0 < m := by
    rw [hsTrajectory]
    exact not_mem_checkerOriginShiftExceptionEvent hnotException
  have htargetStruct : oneStepRecenter s ∈
      firstStructuralPast (shiftedCheckerTarget d) m gaps := by
    rw [← hsTrajectory]
    simpa only [shiftedCheckerTarget, shiftedCheckerTiling] using
      firstStructuralPast_oneStepRecenter_of_origin_lt omega d m (by omega)
        gaps horigin (by simpa only [hsTrajectory] using hstruct)
  have htargetEventCandidate : oneStepRecenter s ∈
      (firstCheckerStructuralTargetFamily d m gaps a low e hm hwindow harithmetic
        hwidth hexternalArithmetic).someCandidate := by
    unfold firstCheckerStructuralTargetFamily
    rw [completeOriginSafeEventTargetFamily_someCandidate_eq a low e
      (firstStructuralPast (shiftedCheckerTarget d) m gaps)
      (measurableSet_firstStructuralPast (shiftedCheckerTarget d) m gaps)
      (fun eta ↦ firstStructuralPast_distinguishedInvariant eta hm gaps)
      (firstStructuralPast_prefixInvariant (shiftedCheckerTarget d) m gaps)
      hm (by omega) hwindow harithmetic hwidth hexternalArithmetic]
    exact ⟨htargetCandidate, htargetStruct⟩
  unfold firstCheckerStructuralFamily
  rw [StoppedHistoryCandidateFamily.someCandidate_checkerFixedPrefixFamily]
  exact ⟨hfirst, htargetEventCandidate⟩

noncomputable def secondCheckerStructuralTargetFamily
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (a : GapScale) (low : ℕ) (e : Direction) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (History (shiftedCheckerTarget d) .even m 3
        (SourceSupportAt (shiftedCheckerTarget d) .even m)) Point
      ((targetOriginSafe m 3 e ∩ thresholdReachStage m 3) ∩
        secondStructuralPast (shiftedCheckerTarget d) m gaps)
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  completeOriginSafeEventTargetFamily a low e
    (secondStructuralPast (shiftedCheckerTarget d) m gaps)
    (measurableSet_secondStructuralPast (shiftedCheckerTarget d) m gaps)
    (fun eta ↦ secondStructuralPast_distinguishedInvariant eta hm gaps)
    (secondStructuralPast_prefixInvariant (shiftedCheckerTarget d) m gaps)
    hm (by omega) hwindow harithmetic hwidth hexternalArithmetic

theorem secondCheckerStructuralTargetFamily_near_measurable
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (a : GapScale) (low : ℕ) (e : Direction) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    ∀ h candidate, MeasurableSet
      ((secondCheckerStructuralTargetFamily d m gaps a low e hm hwindow
        harithmetic hwidth hexternalArithmetic).near h candidate) :=
  completeOriginSafeEventTargetFamily_near_measurable a low e
    (secondStructuralPast (shiftedCheckerTarget d) m gaps)
    (measurableSet_secondStructuralPast (shiftedCheckerTarget d) m gaps)
    (fun eta ↦ secondStructuralPast_distinguishedInvariant eta hm gaps)
    (secondStructuralPast_prefixInvariant (shiftedCheckerTarget d) m gaps)
    hm (by omega) hwindow harithmetic hwidth hexternalArithmetic

noncomputable def secondCheckerStructuralFamily
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (a : GapScale) (low : ℕ) (e : Direction) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :=
  checkerFixedPrefixFamily e
    (secondCheckerStructuralTargetFamily d m gaps a low e hm hwindow harithmetic
      hwidth hexternalArithmetic)
    (secondCheckerStructuralTargetFamily_near_measurable d m gaps a low e hm
      hwindow harithmetic hwidth hexternalArithmetic)

theorem secondCheckerStructuralFamily_someCandidate_subset_complete
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (a : GapScale) (low : ℕ) (e : Direction) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (secondCheckerStructuralFamily d m gaps a low e hm hwindow harithmetic hwidth
        hexternalArithmetic).someCandidate ⊆
      (checkerCompleteOriginSafeFamily
        (t := shiftedCheckerTarget d) (o := .even) (k := 3) a low e hm
          (by omega) hwindow harithmetic hwidth
            hexternalArithmetic).someCandidate := by
  intro s hs
  unfold secondCheckerStructuralFamily at hs
  rw [StoppedHistoryCandidateFamily.someCandidate_checkerFixedPrefixFamily] at hs
  rw [checkerCompleteOriginSafeFamily_someCandidate]
  refine ⟨hs.1, ?_⟩
  exact (completeOriginSafeEventTargetFamily_someCandidate_eq a low e
    (secondStructuralPast (shiftedCheckerTarget d) m gaps)
    (measurableSet_secondStructuralPast (shiftedCheckerTarget d) m gaps)
    (fun eta ↦ secondStructuralPast_distinguishedInvariant eta hm gaps)
    (secondStructuralPast_prefixInvariant (shiftedCheckerTarget d) m gaps)
    hm (by omega) hwindow harithmetic hwidth hexternalArithmetic ▸ hs.2).1

theorem secondCheckerStructuralPrevious_inter_valid_subset
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (e : Direction) (hm : 1 < m) :
    checkerPrefixedPreimage e
      ((targetOriginSafe m 3 e ∩ thresholdReachStage m 3) ∩
        secondStructuralPast (shiftedCheckerTarget d) m gaps) ∩
        validStepWalk ⊆
      secondStructuralPast (.checker d) m gaps := by
  intro s hs
  rcases hs with ⟨⟨hfirst, htarget⟩, hvalid⟩
  rcases htarget with ⟨⟨hsafe, _hreach⟩, hstruct⟩
  let omega := stepsOfWalk s
  have hsTrajectory : trajectory omega = s := hvalid
  have hfirstEq : trajectory omega 1 = directionVector e := by
    rw [hsTrajectory]
    exact hfirst
  rw [← hsTrajectory]
  apply secondStructuralPast_of_oneStepRecenter_of_originSafe omega d e m
    (by omega) gaps hfirstEq
  · simpa only [hsTrajectory] using hsafe
  · simpa only [hsTrajectory, shiftedCheckerTarget, shiftedCheckerTiling]
      using hstruct

theorem secondCheckerStructuralPrevious_measure_le
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (e : Direction) (hm : 1 < m) :
    simpleRandomWalk (checkerPrefixedPreimage e
      ((targetOriginSafe m 3 e ∩ thresholdReachStage m 3) ∩
        secondStructuralPast (shiftedCheckerTarget d) m gaps)) ≤
      simpleRandomWalk (secondStructuralPast (.checker d) m gaps) := by
  let previous := checkerPrefixedPreimage e
    ((targetOriginSafe m 3 e ∩ thresholdReachStage m 3) ∩
      secondStructuralPast (shiftedCheckerTarget d) m gaps)
  have hprevious : MeasurableSet previous :=
    measurableSet_checkerPrefixedPreimage
      (((measurableSet_targetOriginSafe m 3 e).inter
        (measurableSet_thresholdReachStage m 3)).inter
        (measurableSet_secondStructuralPast (shiftedCheckerTarget d) m gaps)) e
  rw [← TilingValidTraceCappedStageAdapter.simpleRandomWalk_inter_validStepWalk
    previous hprevious]
  exact measure_mono
    (secondCheckerStructuralPrevious_inter_valid_subset d m gaps e hm)

theorem checkerComplete_inter_secondStructural_inter_valid_subset
    (d : Tilings.CheckerDirection) (m : ℕ) (gaps : GapTriple)
    (a : GapScale) (low : ℕ) (e : Direction) (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (checkerCompleteOriginSafeFamily
      (t := shiftedCheckerTarget d) (o := .even) (k := 3) a low e hm
        (by omega) hwindow harithmetic hwidth
          hexternalArithmetic).someCandidate ∩
        secondStructuralPast (.checker d) m gaps ∩ validStepWalk ⊆
      (secondCheckerStructuralFamily d m gaps a low e hm hwindow harithmetic
        hwidth hexternalArithmetic).someCandidate := by
  intro s hs
  rcases hs with ⟨⟨hcomplete, hstruct⟩, hvalid⟩
  rw [checkerCompleteOriginSafeFamily_someCandidate] at hcomplete
  rcases hcomplete with ⟨hfirst, htargetCandidate⟩
  have htargetPrevious := someCandidate_subset_previous
    (completeOriginSafeTargetFamily
      (t := shiftedCheckerTarget d) (o := .even) (k := 3) a low e hm
        (by omega) hwindow harithmetic hwidth
          hexternalArithmetic) htargetCandidate
  have hnotException : s ∈
      (checkerOriginShiftExceptionEvent d m 3 0)ᶜ :=
    checkerPrefixedPreimage_targetOriginSafe_subset_exception_compl d e hm
      (by omega) ⟨⟨hfirst, htargetPrevious⟩, hvalid⟩
  let omega := stepsOfWalk s
  have hsTrajectory : trajectory omega = s := hvalid
  have horigin : localTime (trajectory omega)
      (creationTimeNat m 3 (trajectory omega)) 0 < m := by
    rw [hsTrajectory]
    exact not_mem_checkerOriginShiftExceptionEvent hnotException
  have htargetStruct : oneStepRecenter s ∈
      secondStructuralPast (shiftedCheckerTarget d) m gaps := by
    rw [← hsTrajectory]
    simpa only [shiftedCheckerTarget, shiftedCheckerTiling] using
      secondStructuralPast_oneStepRecenter_of_origin_lt omega d m (by omega)
        gaps horigin (by simpa only [hsTrajectory] using hstruct)
  have htargetEventCandidate : oneStepRecenter s ∈
      (secondCheckerStructuralTargetFamily d m gaps a low e hm hwindow
        harithmetic hwidth hexternalArithmetic).someCandidate := by
    unfold secondCheckerStructuralTargetFamily
    rw [completeOriginSafeEventTargetFamily_someCandidate_eq a low e
      (secondStructuralPast (shiftedCheckerTarget d) m gaps)
      (measurableSet_secondStructuralPast (shiftedCheckerTarget d) m gaps)
      (fun eta ↦ secondStructuralPast_distinguishedInvariant eta hm gaps)
      (secondStructuralPast_prefixInvariant (shiftedCheckerTarget d) m gaps)
      hm (by omega) hwindow harithmetic hwidth hexternalArithmetic]
    exact ⟨htargetCandidate, htargetStruct⟩
  unfold secondCheckerStructuralFamily
  rw [StoppedHistoryCandidateFamily.someCandidate_checkerFixedPrefixFamily]
  exact ⟨hfirst, htargetEventCandidate⟩

end

end Erdos1165.HLOZCheckerStructuralPastProp49Row
