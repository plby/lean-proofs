/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCheckerOriginSafeDistinguishedProp49Family
import ErdosProblems.Erdos1165.HLOZSourceRefinementEventRestriction
import ErdosProblems.Erdos1165.HLOZSourceSelectedRefinementEventRestriction

/-!
# Origin-safe checker source families conditioned on a structural event

The exposed-origin and distinguished-origin source refinements are each
restricted by an event determined by the distinguished coordinates.  Their
disjoint recombination preserves the original Proposition 4.9 ratio.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCheckerOriginSafeEventProp49Family

open HLOZCheckerOriginSafeDistinguishedProp49Family
open HLOZCheckerOriginSafeProp49Family
open HLOZFilteredOrientedAllCreationStoppedCandidateFamily
open HLOZMeshCandidatePolynomialNumerics
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents
open HLOZPrefixedAllCreationDistinguishedRestriction
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceDistinguishedEventProp49Family
open HLOZSourceRefinementEventRestriction
open HLOZSourceSelectedRefinementEventRestriction
open HLOZStoppedHistoryCandidateFuture
open HLOZTypedStoppedCandidateConditionalProduct
open LazyDecomposition
open TilingConditionalCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The complete origin-safe narrow event, additionally conditioned on a
distinguished-coordinate event. -/
noncomputable def completeOriginSafeEventCandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (e : Direction) (event : Set WalkPath)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (candidate : Point) : Set WalkPath :=
  completeOriginSafeCandidateNear eta a low e hm hk hwindow harithmetic
      hexternalArithmetic candidate

theorem measurableSet_completeOriginSafeEventCandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (e : Direction) (event : Set WalkPath) (hevent : MeasurableSet event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (candidate : Point) :
    MeasurableSet (completeOriginSafeEventCandidateNear eta a low e event hm
      hk hwindow harithmetic hexternalArithmetic candidate) := by
  exact measurableSet_completeOriginSafeCandidateNear eta a low e hm hk
    hwindow harithmetic hexternalArithmetic candidate

/-- Complete origin-safe source family whose literal previous event is the
origin-safe reaching stage intersected with `event`. -/
noncomputable def completeOriginSafeEventTargetFamily
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (event : Set WalkPath) (hevent : MeasurableSet event)
    (hinvariant : ∀ eta : SourceSupportedIndex t o m k,
      SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (History t o m k (SourceSupportAt t o m)) Point
      ((targetOriginSafe m k e ∩ thresholdReachStage m k) ∩ event)
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) where
  piece := historyPiece t o m k (SourceSupportAt t o m)
    ((targetOriginSafe m k e ∩ thresholdReachStage m k) ∩ event)
  candidates := filteredHistoryCandidates t o m k (SourceSupportAt t o m)
    SourceProp49EligibleHistory
  near := fun h candidate ↦ match h with
    | none => ∅
    | some eta => completeOriginSafeEventCandidateNear eta a low e event hm hk
        hwindow harithmetic hexternalArithmetic candidate
  piece_pairwise := historyPiece_pairwise t o m k (SourceSupportAt t o m)
    ((targetOriginSafe m k e ∩ thresholdReachStage m k) ∩ event)
  piece_measurable := measurableSet_historyPiece t o m k
    (SourceSupportAt t o m)
    ((targetOriginSafe m k e ∩ thresholdReachStage m k) ∩ event)
    (((measurableSet_targetOriginSafe m k e).inter
      (measurableSet_thresholdReachStage m k)).inter hevent)
    (orientedAllCreationConcreteFamily t o m k (SourceSupportAt t o m)
      (SourceSupportData t o m k))
  piece_union := iUnion_historyPiece t o m k (SourceSupportAt t o m)
    ((targetOriginSafe m k e ∩ thresholdReachStage m k) ∩ event)
  candidate_card := by
    intro h
    cases h with
    | none => simp [filteredHistoryCandidates]
    | some eta =>
        classical
        by_cases heligible : SourceProp49EligibleHistory eta
        · simpa [filteredHistoryCandidates, heligible] using heligible.card_le
        · simp [filteredHistoryCandidates, heligible]
  coordinate_ratio := by
    intro h candidate hcandidate
    cases h with
    | none => simp [filteredHistoryCandidates] at hcandidate
    | some eta =>
        have heligible := (mem_filteredHistoryCandidates_some_iff t o m k
          (SourceSupportAt t o m) SourceProp49EligibleHistory eta candidate).mp
            hcandidate
        have hpiece := measurableSet_historyPiece t o m k
          (SourceSupportAt t o m)
          ((targetOriginSafe m k e ∩ thresholdReachStage m k) ∩ event)
          (((measurableSet_targetOriginSafe m k e).inter
            (measurableSet_thresholdReachStage m k)).inter hevent)
          (orientedAllCreationConcreteFamily t o m k (SourceSupportAt t o m)
            (SourceSupportData t o m k)) (some eta)
        have hnear := measurableSet_completeOriginSafeEventCandidateNear eta a
          low e event hevent hm hk hwindow harithmetic hexternalArithmetic
          candidate
        apply coordinate_ratio_of_coordinateMassSpec hpiece hnear
          (prop49CandidateRatioEnvelope_ne_top _ _ _)
        by_cases horigin : targetOriginBase t e ∈ eta.1.2
        · let href₀ := sourceOriginSafeRefinement eta a candidate
            heligible.2 low e horigin heligible.1.good hm hk hwindow harithmetic
              hwidth hexternalArithmetic
          let href := restrictSourceRefinementToEvent eta href₀ event
            (hinvariant eta) hprefix hk
          simpa only [completeOriginSafeEventCandidateNear,
            completeOriginSafeCandidateNear, heligible.1, horigin,
            sourceOriginSafeCandidateNear, heligible.2, dite_true,
            historyPiece, inter_assoc, inter_left_comm, inter_comm] using
            (coordinateMassSpecOfAllCreation
              (withSelected (SourceFiber eta) (fun cap d ↦
                (SourceFiber eta).selected cap d ∧
                  distinguishedEventSafe eta event cap d)) href)
        · let priorSafe := fun cap d ↦
            (SourceFiber eta).selected cap d ∧
              distinguishedTargetOriginSafe eta e cap d
          have hdistEligible : DistinguishedOriginSafeEligibleHistory e eta :=
            ⟨heligible.1, horigin⟩
          let href₀ := sourceDistinguishedOriginSafeRefinement eta a
            candidate heligible.2 low heligible.1.good e horigin hm hk hwindow
              harithmetic hexternalArithmetic
          let href := restrictSelectedSourceRefinementToEvent eta priorSafe
            href₀ event (hinvariant eta) hprefix hk
          simpa only [completeOriginSafeEventCandidateNear,
            completeOriginSafeCandidateNear, heligible.1, horigin,
            sourceDistinguishedOriginSafeCandidateNear, hdistEligible,
            heligible.2,
            dite_true, dite_false, historyPiece, inter_assoc, inter_left_comm,
            inter_comm] using
            (coordinateMassSpecOfAllCreation
              (withSelected (withSelected (SourceFiber eta) priorSafe)
                (fun cap d ↦
                  (withSelected (SourceFiber eta) priorSafe).selected cap d ∧
                    distinguishedEventSafe eta event cap d)) href)

theorem completeOriginSafeEventTargetFamily_near_measurable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (event : Set WalkPath) (hevent : MeasurableSet event)
    (hinvariant : ∀ eta : SourceSupportedIndex t o m k,
      SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    ∀ h candidate, MeasurableSet
      ((completeOriginSafeEventTargetFamily (t := t) (o := o) a low e event
        hevent hinvariant hprefix hm hk hwindow harithmetic hwidth
          hexternalArithmetic).near h candidate) := by
  intro h candidate
  cases h with
  | none => exact MeasurableSet.empty
  | some eta =>
      exact measurableSet_completeOriginSafeEventCandidateNear eta a low e
        event hevent hm hk hwindow harithmetic hexternalArithmetic candidate

/-- Exact candidate event: impose `event` on the complete origin-safe target
candidate union. -/
theorem completeOriginSafeEventTargetFamily_someCandidate_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (event : Set WalkPath) (hevent : MeasurableSet event)
    (hinvariant : ∀ eta : SourceSupportedIndex t o m k,
      SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (completeOriginSafeEventTargetFamily (t := t) (o := o) a low e event
      hevent hinvariant hprefix hm hk hwindow harithmetic hwidth
        hexternalArithmetic).someCandidate =
      (completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
        harithmetic hwidth hexternalArithmetic).someCandidate ∩ event := by
  apply Set.Subset.antisymm
  · intro s hs
    unfold StoppedHistoryCandidateFamily.someCandidate at hs ⊢
    rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨candidate, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨hcandidate, hpiece, hnear⟩
    cases h with
    | none =>
        change candidate ∈ (∅ : Finset Point) at hcandidate
        simp at hcandidate
    | some eta =>
        refine ⟨Set.mem_iUnion_of_mem (some eta) <|
          Set.mem_iUnion_of_mem candidate <|
            Set.mem_iUnion_of_mem hcandidate ⟨?_, hnear⟩, hpiece.1.2⟩
        simpa only [historyPiece] using ⟨hpiece.1.1, hpiece.2⟩
  · rintro s ⟨hs, heventS⟩
    unfold StoppedHistoryCandidateFamily.someCandidate at hs ⊢
    rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨candidate, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨hcandidate, hpiece, hnear⟩
    cases h with
    | none =>
        change candidate ∈ (∅ : Finset Point) at hcandidate
        simp at hcandidate
    | some eta =>
        refine Set.mem_iUnion_of_mem (some eta) <|
          Set.mem_iUnion_of_mem candidate <|
            Set.mem_iUnion_of_mem hcandidate ⟨?_, hnear⟩
        simpa only [historyPiece] using ⟨⟨hpiece.1, heventS⟩, hpiece.2⟩

end

end Erdos1165.HLOZCheckerOriginSafeEventProp49Family
