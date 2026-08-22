/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZConcreteSourceThetaSeriesAdapter
import ErdosProblems.Erdos1165.HLOZHeterogeneousFilteredTransitionFactors
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairBalanceSeriesAdapter
import ErdosProblems.Erdos1165.HLOZStructuralPastTilingEndpointSourceRowObservability
import ErdosProblems.Erdos1165.HLOZTilingEndpointSourceRowEventualParameters
import ErdosProblems.Erdos1165.HLOZTilingEndpointSourceRowRankOneObservability

/-!
# Additive recurrence through the structural HLOZ pasts

Low mesh coordinates are estimated relative to the structural predecessor,
which is slightly larger than the cumulatively filtered predecessor.  The
difference consists only of the staged source candidate and is therefore
summable.  This file carries those additive payments through the three ranks
and recovers a summable cubic terminal bound.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.HLOZStructuralPastAdditiveRecurrence

open HLOZConcreteSourceThetaSeriesAdapter
open HLOZFilteredTransitionAssembly HLOZHeterogeneousFilteredTransitionFactors
open HLOZHighSpatialTransitionFactor HLOZMeshCandidateFutureFactor
open HLOZMeshCandidatePolynomialNumerics HLOZNoLazyFilteredPastObservability
open HLOZNoLazyFilteredTransitions HLOZNoLazyHighSpatialTransitionFactor
open HLOZNoLazyFiniteSourceRowUpperAssembly HLOZPathEvents
open HLOZNoLazyFullGapSeriesAssembly
open HLOZNoLazyHeterogeneousTransitionFactors
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZPositiveInterfacePairBalanceSeriesAdapter
open HLOZPrefixedProp49CandidateWindowRatio HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion HLOZRawOrientedSourceThetaPayment
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceCorrectFullGapClosure HLOZSourceStructuralPastInvariant
open HLOZStoppedHistoryCandidateFuture
open HLOZStructuralPastTilingEndpointSourceRowObservability
open HLOZTilingEndpointSourceRowEventualParameters
open HLOZTilingEndpointSourceRowRankOneObservability
open LazyDecomposition ScreeningInstantiation
open TerminalParameterBounds

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple
abbrev BranchEvent := HLOZFilteredTransitionAssembly.BranchEvent

/-- The canonical one-step cost with constant one never exceeds one. -/
theorem hlozTransitionCost_one_le_one (m : ℕ) :
    UpperCanonical.hlozTransitionCost 1 m ≤ 1 := by
  unfold UpperCanonical.hlozTransitionCost UpperAssembly.pSeriesWeight
  simp only [ENNReal.coe_one, one_mul]
  apply ENNReal.ofReal_le_one.mpr
  have hkappa : 0 ≤ kappa :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1 / 3)
      hloz_parameter_inequalities.2.2.2.2.2.2.1.le
  have hbase : 1 ≤ |(m : ℝ) + 1| := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
    norm_num
  exact (div_le_one (Real.rpow_pos_of_pos
    (by positivity : (0 : ℝ) < |(m : ℝ) + 1|) kappa)).2
      (Real.one_le_rpow hbase hkappa)

/-- A set is covered by the part outside a payment and the payment. -/
theorem measure_le_diff_add (event payment : Set WalkPath) :
    simpleRandomWalk event ≤
      simpleRandomWalk (event \ payment) + simpleRandomWalk payment := by
  calc
    simpleRandomWalk event ≤
        simpleRandomWalk ((event \ payment) ∪ payment) := by
      apply measure_mono
      intro s hs
      by_cases hp : s ∈ payment
      · exact Or.inr hp
      · exact Or.inl ⟨hs, hp⟩
    _ ≤ simpleRandomWalk (event \ payment) + simpleRandomWalk payment :=
      measure_union_le _ _

/-- The first filtered event is contained in its structural predecessor. -/
theorem filteredFirstTransitionEvent_subset_firstStructuralPast
    (stagedCandidate₁ : BranchEvent) (t : DominoTiling) (m : ℕ)
    (gaps : GapTriple) :
    filteredFirstTransitionEvent stagedCandidate₁ t m gaps ⊆
      firstStructuralPast t m gaps := by
  intro s hs
  exact ⟨hs.1, fun hbad ↦ hs.2 (Or.inl hbad)⟩

/-- The second filtered event is contained in the rank-three structural
predecessor. -/
theorem filteredSecondTransitionEvent_subset_secondStructuralPast
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) :
    filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
        t m gaps ⊆ secondStructuralPast t m gaps := by
  intro s hs
  exact ⟨hs.1, fun hbad ↦ hs.2 <|
    hbad.elim (fun h ↦ Or.inl (Or.inl h))
      (fun h ↦ Or.inr (Or.inl h))⟩

/-- The only part of the first structural predecessor removed by the first
filter, besides the structural low-gap event itself, is the first staged
candidate. -/
theorem firstStructuralPast_subset_filteredFirst_union_candidate
    (stagedCandidate₁ : BranchEvent) (t : DominoTiling) (m : ℕ)
    (gaps : GapTriple) :
    firstStructuralPast t m gaps ⊆
      filteredFirstTransitionEvent stagedCandidate₁ t m gaps ∪
        stagedCandidate₁ t m gaps := by
  intro s hs
  by_cases hcandidate : s ∈ stagedCandidate₁ t m gaps
  · exact Or.inr hcandidate
  · apply Or.inl
    exact ⟨hs.1, fun hbad ↦ hbad.elim hs.2 hcandidate⟩

/-- The second structural predecessor differs from the cumulatively filtered
second event only by the first two staged candidates. -/
theorem secondStructuralPast_subset_filteredSecond_union_candidates
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) :
    secondStructuralPast t m gaps ⊆
      filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
          t m gaps ∪
        (stagedCandidate₁ t m gaps ∪ stagedCandidate₂ t m gaps) := by
  intro s hs
  by_cases hcandidate₁ : s ∈ stagedCandidate₁ t m gaps
  · exact Or.inr (Or.inl hcandidate₁)
  by_cases hcandidate₂ : s ∈ stagedCandidate₂ t m gaps
  · exact Or.inr (Or.inr hcandidate₂)
  · apply Or.inl
    refine ⟨hs.1, ?_⟩
    rintro ((hlow₁ | hcandidate₁') | (hlow₂ | hcandidate₂'))
    · exact hs.2 (Or.inl hlow₁)
    · exact hcandidate₁ hcandidate₁'
    · exact hs.2 (Or.inr hlow₂)
    · exact hcandidate₂ hcandidate₂'

theorem measure_firstStructuralPast_le_filteredFirst_add_candidate
    (stagedCandidate₁ : BranchEvent) (t : DominoTiling) (m : ℕ)
    (gaps : GapTriple) :
    simpleRandomWalk (firstStructuralPast t m gaps) ≤
      simpleRandomWalk
          (filteredFirstTransitionEvent stagedCandidate₁ t m gaps) +
        simpleRandomWalk (stagedCandidate₁ t m gaps) := by
  exact (measure_mono
    (firstStructuralPast_subset_filteredFirst_union_candidate
      stagedCandidate₁ t m gaps)).trans (measure_union_le _ _)

theorem measure_secondStructuralPast_le_filteredSecond_add_candidates
    (stagedCandidate₁ stagedCandidate₂ : BranchEvent)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) :
    simpleRandomWalk (secondStructuralPast t m gaps) ≤
      simpleRandomWalk
          (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
            t m gaps) +
        simpleRandomWalk (stagedCandidate₁ t m gaps) +
          simpleRandomWalk (stagedCandidate₂ t m gaps) := by
  calc
    simpleRandomWalk (secondStructuralPast t m gaps) ≤
        simpleRandomWalk
          (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
              t m gaps ∪
            (stagedCandidate₁ t m gaps ∪ stagedCandidate₂ t m gaps)) :=
      measure_mono
        (secondStructuralPast_subset_filteredSecond_union_candidates
          stagedCandidate₁ stagedCandidate₂ t m gaps)
    _ ≤ simpleRandomWalk
          (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
            t m gaps) +
        simpleRandomWalk
          (stagedCandidate₁ t m gaps ∪ stagedCandidate₂ t m gaps) :=
      measure_union_le _ _
    _ ≤ simpleRandomWalk
          (filteredSecondTransitionEvent stagedCandidate₁ stagedCandidate₂
            t m gaps) +
        (simpleRandomWalk (stagedCandidate₁ t m gaps) +
          simpleRandomWalk (stagedCandidate₂ t m gaps)) := by
      gcongr
      exact measure_union_le _ _
    _ = _ := by ac_rfl

/-! ## Rankwise additive transition bounds -/

theorem measure_filteredFirst_diff_payment_le_transition
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.1.1 ∈ properGapMesh) (hlow : gaps.1.1 ∈ lowGapMesh)
    (hm : 1 < m) (hwindow : Prop49WindowArithmeticAt m gaps.1.1)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hnumeric : (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope (6 * prop49WindowRatioConstant) m gaps.1.1 *
        meshEscapeCost m gaps.1.1 ≤ UpperCanonical.hlozTransitionCost 1 m) :
    simpleRandomWalk
        (filteredFirstTransitionEvent (firstRawStagedCandidate data) t m gaps \
          rawOrientedSourceThetaTotalPaymentAtRank data t 1 m) ≤
      UpperCanonical.hlozTransitionCost 1 m := by
  have h := HeterogeneousFiniteSourceRowMeshLowCoordinateData.transitionFactor
    (firstPaymentFilteredFiniteRowMeshLowCoordinateData data t m gaps low
      hproper hlow hm hwindow harithmetic hwidth hexternalArithmetic)
        (by omega) hnumeric
  have hbound := h.measure_next_le MeasurableSet.univ
  simpa using hbound

theorem measure_filteredFirst_le_transition_add_payment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.1.1 ∈ properGapMesh)
    (hm : 1 < m)
    (hwindow : gaps.1.1 ∈ lowGapMesh → Prop49WindowArithmeticAt m gaps.1.1)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hnumeric : gaps.1.1 ∈ lowGapMesh → (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope (6 * prop49WindowRatioConstant) m gaps.1.1 *
        meshEscapeCost m gaps.1.1 ≤ UpperCanonical.hlozTransitionCost 1 m)
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost 1 m) :
    simpleRandomWalk
        (filteredFirstTransitionEvent (firstRawStagedCandidate data) t m gaps) ≤
      UpperCanonical.hlozTransitionCost 1 m +
        simpleRandomWalk
          (rawOrientedSourceThetaTotalPaymentAtRank data t 1 m) := by
  by_cases hhigh : gaps.1.1 ∈ highGapMesh
  · have hfactor := noLazyFilteredFirstHighSourceCorrectTransitionFactor
      (firstRawStagedCandidate data) 1 t m gaps (by omega) hhigh
        (measurableSet_firstRawStagedCandidate data t m gaps) hcost
    have hbound := hfactor.measure_next_le MeasurableSet.univ
      (measurableSet_filteredFirstTransitionEvent
        (firstRawStagedCandidate data) t m gaps
          (measurableSet_firstRawStagedCandidate data t m gaps))
    have hfirst : simpleRandomWalk
        (filteredFirstTransitionEvent (firstRawStagedCandidate data) t m gaps) ≤
          UpperCanonical.hlozTransitionCost 1 m := by
      simpa using hbound
    exact hfirst.trans (le_add_right le_rfl)
  · have hlow :=
      (mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right hhigh
    calc
      simpleRandomWalk
          (filteredFirstTransitionEvent (firstRawStagedCandidate data) t m gaps) ≤
          simpleRandomWalk
              (filteredFirstTransitionEvent (firstRawStagedCandidate data)
                  t m gaps \
                rawOrientedSourceThetaTotalPaymentAtRank data t 1 m) +
            simpleRandomWalk
              (rawOrientedSourceThetaTotalPaymentAtRank data t 1 m) :=
        measure_le_diff_add _ _
      _ ≤ UpperCanonical.hlozTransitionCost 1 m +
            simpleRandomWalk
              (rawOrientedSourceThetaTotalPaymentAtRank data t 1 m) :=
        add_le_add
          (measure_filteredFirst_diff_payment_le_transition data t m gaps low
            hproper hlow hm (hwindow hlow) harithmetic hwidth
              hexternalArithmetic (hnumeric hlow)) le_rfl

theorem measure_filteredSecond_le_transition_mul_structuralPast_add_payment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.1.2 ∈ properGapMesh)
    (hm : 1 < m)
    (hwindow : gaps.1.2 ∈ lowGapMesh → Prop49WindowArithmeticAt m gaps.1.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hnumeric : gaps.1.2 ∈ lowGapMesh → (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope (6 * prop49WindowRatioConstant) m gaps.1.2 *
        meshEscapeCost m gaps.1.2 ≤ UpperCanonical.hlozTransitionCost 1 m)
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost 1 m) :
    simpleRandomWalk
        (filteredSecondTransitionEvent (firstRawStagedCandidate data)
          (secondRawStagedCandidate data) t m gaps) ≤
      UpperCanonical.hlozTransitionCost 1 m *
          simpleRandomWalk (firstStructuralPast t m gaps) +
        simpleRandomWalk
          (rawOrientedSourceThetaTotalPaymentAtRank data t 2 m) := by
  by_cases hhigh : gaps.1.2 ∈ highGapMesh
  · have hfactor := noLazyFilteredSecondHighSourceCorrectTransitionFactor
      (firstRawStagedCandidate data) (secondRawStagedCandidate data) 1
        t m gaps (by omega) hhigh
        (measurableSet_firstRawStagedCandidate data t m gaps)
        (measurableSet_secondRawStagedCandidate data t m gaps)
        (pairCreationAtom_inter_firstRawStagedCandidate_observable data t m gaps)
        hcost
    have hbound := hfactor.measure_next_le
      (measurableSet_filteredFirstTransitionEvent
        (firstRawStagedCandidate data) t m gaps
          (measurableSet_firstRawStagedCandidate data t m gaps))
      (measurableSet_filteredSecondTransitionEvent
        (firstRawStagedCandidate data) (secondRawStagedCandidate data)
          t m gaps (measurableSet_firstRawStagedCandidate data t m gaps)
            (measurableSet_secondRawStagedCandidate data t m gaps))
    calc
      simpleRandomWalk
          (filteredSecondTransitionEvent (firstRawStagedCandidate data)
            (secondRawStagedCandidate data) t m gaps) ≤
          UpperCanonical.hlozTransitionCost 1 m *
            simpleRandomWalk
              (filteredFirstTransitionEvent (firstRawStagedCandidate data)
                t m gaps) := hbound
      _ ≤ UpperCanonical.hlozTransitionCost 1 m *
          simpleRandomWalk (firstStructuralPast t m gaps) := by
        simpa only [mul_comm] using mul_le_mul_right
          (measure_mono
            (filteredFirstTransitionEvent_subset_firstStructuralPast
              (firstRawStagedCandidate data) t m gaps))
          (UpperCanonical.hlozTransitionCost 1 m)
      _ ≤ _ := le_add_right le_rfl
  · have hlow :=
      (mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right hhigh
    calc
      simpleRandomWalk
          (filteredSecondTransitionEvent (firstRawStagedCandidate data)
            (secondRawStagedCandidate data) t m gaps) ≤
          simpleRandomWalk
              (filteredSecondTransitionEvent (firstRawStagedCandidate data)
                  (secondRawStagedCandidate data) t m gaps \
                rawOrientedSourceThetaTotalPaymentAtRank data t 2 m) +
            simpleRandomWalk
              (rawOrientedSourceThetaTotalPaymentAtRank data t 2 m) :=
        measure_le_diff_add _ _
      _ ≤ _ := add_le_add
        (measure_filteredSecond_diff_payment_le_transition_mul_structuralPast
          data t m gaps low hproper hlow hm (hwindow hlow) harithmetic hwidth
            hexternalArithmetic (hnumeric hlow)) le_rfl

theorem measure_filteredThird_le_transition_mul_structuralPast_add_payment
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper : gaps.2 ∈ properGapMesh)
    (hm : 1 < m)
    (hwindow : gaps.2 ∈ lowGapMesh → Prop49WindowArithmeticAt m gaps.2)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hnumeric : gaps.2 ∈ lowGapMesh → (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope (6 * prop49WindowRatioConstant) m gaps.2 *
        meshEscapeCost m gaps.2 ≤ UpperCanonical.hlozTransitionCost 1 m)
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost 1 m) :
    simpleRandomWalk
        (filteredThirdTransitionEvent (firstRawStagedCandidate data)
          (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
            t m gaps) ≤
      UpperCanonical.hlozTransitionCost 1 m *
          simpleRandomWalk (secondStructuralPast t m gaps) +
        simpleRandomWalk
          (rawOrientedSourceThetaTotalPaymentAtRank data t 3 m) := by
  by_cases hhigh : gaps.2 ∈ highGapMesh
  · have hfactor := noLazyFilteredThirdHighSourceCorrectTransitionFactor
      (firstRawStagedCandidate data) (secondRawStagedCandidate data)
        (thirdRawStagedCandidate data) 1 t m gaps (by omega) hhigh
        (measurableSet_firstRawStagedCandidate data t m gaps)
        (measurableSet_secondRawStagedCandidate data t m gaps)
        (measurableSet_thirdRawStagedCandidate data t m gaps)
        (tripleCreationAtom_inter_firstRawStagedCandidate_observable data t m gaps)
        (tripleCreationAtom_inter_secondRawStagedCandidate_observable data t m gaps)
        hcost
    have hbound := hfactor.measure_next_le
      (measurableSet_filteredSecondTransitionEvent
        (firstRawStagedCandidate data) (secondRawStagedCandidate data)
          t m gaps (measurableSet_firstRawStagedCandidate data t m gaps)
            (measurableSet_secondRawStagedCandidate data t m gaps))
      (measurableSet_filteredThirdTransitionEvent
        (firstRawStagedCandidate data) (secondRawStagedCandidate data)
          (thirdRawStagedCandidate data) t m gaps
            (measurableSet_firstRawStagedCandidate data t m gaps)
            (measurableSet_secondRawStagedCandidate data t m gaps)
            (measurableSet_thirdRawStagedCandidate data t m gaps))
    calc
      simpleRandomWalk
          (filteredThirdTransitionEvent (firstRawStagedCandidate data)
            (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
              t m gaps) ≤
          UpperCanonical.hlozTransitionCost 1 m *
            simpleRandomWalk
              (filteredSecondTransitionEvent (firstRawStagedCandidate data)
                (secondRawStagedCandidate data) t m gaps) := hbound
      _ ≤ UpperCanonical.hlozTransitionCost 1 m *
          simpleRandomWalk (secondStructuralPast t m gaps) := by
        simpa only [mul_comm] using mul_le_mul_right
          (measure_mono
            (filteredSecondTransitionEvent_subset_secondStructuralPast
              (firstRawStagedCandidate data) (secondRawStagedCandidate data)
                t m gaps))
          (UpperCanonical.hlozTransitionCost 1 m)
      _ ≤ _ := le_add_right le_rfl
  · have hlow :=
      (mem_lowGapMesh_or_highGapMesh_of_mem_proper hproper).resolve_right hhigh
    calc
      simpleRandomWalk
          (filteredThirdTransitionEvent (firstRawStagedCandidate data)
            (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
              t m gaps) ≤
          simpleRandomWalk
              (filteredThirdTransitionEvent (firstRawStagedCandidate data)
                  (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
                    t m gaps \
                rawOrientedSourceThetaTotalPaymentAtRank data t 3 m) +
            simpleRandomWalk
              (rawOrientedSourceThetaTotalPaymentAtRank data t 3 m) :=
        measure_le_diff_add _ _
      _ ≤ _ := add_le_add
        (measure_filteredThird_diff_payment_le_transition_mul_structuralPast
          data t m gaps low hproper hlow hm (hwindow hlow) harithmetic hwidth
            hexternalArithmetic (hnumeric hlow)) le_rfl

/-- Pure `ENNReal` bookkeeping for three additive transition estimates. -/
theorem three_step_additive_bound
    {q f₁ s₁ f₂ s₂ f₃ p₁ p₂ p₃ c₁ c₂ : ℝ≥0∞}
    (hq : q ≤ 1)
    (hf₁ : f₁ ≤ q + p₁)
    (hs₁ : s₁ ≤ f₁ + c₁)
    (hf₂ : f₂ ≤ q * s₁ + p₂)
    (hs₂ : s₂ ≤ f₂ + c₁ + c₂)
    (hf₃ : f₃ ≤ q * s₂ + p₃) :
    f₃ ≤ q ^ 3 + (p₁ + c₁) + (p₂ + c₁ + c₂) + p₃ := by
  calc
    f₃ ≤ q * s₂ + p₃ := hf₃
    _ ≤ q * (f₂ + c₁ + c₂) + p₃ := by gcongr
    _ ≤ q * (q * s₁ + p₂ + c₁ + c₂) + p₃ := by gcongr
    _ ≤ q * (q * (f₁ + c₁) + p₂ + c₁ + c₂) + p₃ := by
      gcongr
    _ ≤ q * (q * (q + p₁ + c₁) + p₂ + c₁ + c₂) + p₃ := by
      gcongr
    _ = q ^ 3 + q ^ 2 * (p₁ + c₁) +
          q * (p₂ + c₁ + c₂) + p₃ := by ring
    _ ≤ q ^ 3 + (p₁ + c₁) + (p₂ + c₁ + c₂) + p₃ := by
      have hq2 : q ^ 2 ≤ 1 := pow_le_one₀ bot_le hq
      have hmul2 : q ^ 2 * (p₁ + c₁) ≤ p₁ + c₁ := by
        calc
          q ^ 2 * (p₁ + c₁) ≤ 1 * (p₁ + c₁) :=
            by simpa only [mul_comm] using mul_le_mul_right hq2 (p₁ + c₁)
          _ = p₁ + c₁ := one_mul _
      have hmul1 : q * (p₂ + c₁ + c₂) ≤ p₂ + c₁ + c₂ := by
        calc
          q * (p₂ + c₁ + c₂) ≤ 1 * (p₂ + c₁ + c₂) :=
            by simpa only [mul_comm] using
              mul_le_mul_right hq (p₂ + c₁ + c₂)
          _ = p₂ + c₁ + c₂ := one_mul _
      exact add_le_add (add_le_add (add_le_add le_rfl hmul2) hmul1) le_rfl

/-- The three structural-past estimates recover the same cubic transition
decay, up to the three exact rank payments and the first two staged source
candidates. -/
theorem measure_filteredThird_le_cubic_add_payments_candidates
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) (low : ℕ)
    (hproper₁ : gaps.1.1 ∈ properGapMesh)
    (hproper₂ : gaps.1.2 ∈ properGapMesh)
    (hproper₃ : gaps.2 ∈ properGapMesh)
    (hm : 1 < m)
    (hwindow : ∀ a ∈ lowGapMesh, Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hnumeric₁ : gaps.1.1 ∈ lowGapMesh → (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope (6 * prop49WindowRatioConstant) m gaps.1.1 *
        meshEscapeCost m gaps.1.1 ≤ UpperCanonical.hlozTransitionCost 1 m)
    (hnumeric₂ : gaps.1.2 ∈ lowGapMesh → (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope (6 * prop49WindowRatioConstant) m gaps.1.2 *
        meshEscapeCost m gaps.1.2 ≤ UpperCanonical.hlozTransitionCost 1 m)
    (hnumeric₃ : gaps.2 ∈ lowGapMesh → (initialBudget48 m : ℝ≥0∞) *
      prop49CandidateRatioEnvelope (6 * prop49WindowRatioConstant) m gaps.2 *
        meshEscapeCost m gaps.2 ≤ UpperCanonical.hlozTransitionCost 1 m)
    (hcost : ENNReal.ofReal
      (literalEscapeProbability (highSpatialRadius m)) ≤
        UpperCanonical.hlozTransitionCost 1 m) :
    simpleRandomWalk
        (filteredThirdTransitionEvent (firstRawStagedCandidate data)
          (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
            t m gaps) ≤
      UpperCanonical.hlozTransitionCost 1 m ^ 3 +
          (simpleRandomWalk
              (rawOrientedSourceThetaTotalPaymentAtRank data t 1 m) +
            simpleRandomWalk (firstRawStagedCandidate data t m gaps)) +
        (simpleRandomWalk
              (rawOrientedSourceThetaTotalPaymentAtRank data t 2 m) +
            simpleRandomWalk (firstRawStagedCandidate data t m gaps) +
              simpleRandomWalk (secondRawStagedCandidate data t m gaps)) +
          simpleRandomWalk
            (rawOrientedSourceThetaTotalPaymentAtRank data t 3 m) := by
  apply three_step_additive_bound (hlozTransitionCost_one_le_one m)
  · exact measure_filteredFirst_le_transition_add_payment data t m gaps low
      hproper₁ hm (hwindow gaps.1.1) harithmetic hwidth hexternalArithmetic
        hnumeric₁ hcost
  · exact measure_firstStructuralPast_le_filteredFirst_add_candidate
      (firstRawStagedCandidate data) t m gaps
  · exact
      measure_filteredSecond_le_transition_mul_structuralPast_add_payment
        data t m gaps low hproper₂ hm (hwindow gaps.1.2) harithmetic hwidth
          hexternalArithmetic hnumeric₂ hcost
  · exact measure_secondStructuralPast_le_filteredSecond_add_candidates
      (firstRawStagedCandidate data) (secondRawStagedCandidate data) t m gaps
  · exact measure_filteredThird_le_transition_mul_structuralPast_add_payment
      data t m gaps low hproper₃ hm (hwindow gaps.2) harithmetic hwidth
        hexternalArithmetic hnumeric₃ hcost

/-- A pointwise-finite `ENNReal` family dominated on a cofinite tail by a
summable family is summable. -/
theorem tsum_ne_top_of_eventually_le
    {f g : ℕ → ℝ≥0∞} (hfinite : ∀ m, f m ≠ ∞)
    (hg : ∑' m, g m ≠ ∞) (hfg : ∀ᶠ m : ℕ in atTop, f m ≤ g m) :
    ∑' m, f m ≠ ∞ := by
  rw [eventually_atTop] at hfg
  obtain ⟨N, hN⟩ := hfg
  let small : ℕ → ℝ≥0∞ := fun m ↦ if m < N then f m else 0
  have hsmall : ∑' m, small m ≠ ∞ := by
    rw [tsum_eq_sum (s := Finset.range N)]
    · exact ENNReal.sum_ne_top.mpr fun m hm ↦ by
        simpa only [small, if_pos (Finset.mem_range.mp hm)] using hfinite m
    · intro m hm
      have hmN : ¬m < N := by simpa [Finset.mem_range] using hm
      simp [small, hmN]
  have hmajor : ∑' m, (small m + g m) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hsmall, hg⟩
  apply ne_top_of_le_ne_top hmajor
  apply ENNReal.tsum_le_tsum
  intro m
  by_cases hm : m < N
  · simp [small, hm]
  · have hNm : N ≤ m := Nat.le_of_not_gt hm
    exact (hN m hNm).trans (by simp [small, hm])

/-- The sum of two finite `ENNReal` series is finite. -/
theorem tsum_add_ne_top {f g : ℕ → ℝ≥0∞}
    (hf : ∑' m, f m ≠ ∞) (hg : ∑' m, g m ≠ ∞) :
    ∑' m, (f m + g m) ≠ ∞ := by
  rw [ENNReal.tsum_add]
  exact ENNReal.add_ne_top.mpr ⟨hf, hg⟩

/-! ## Branchwise summability -/

theorem filteredThirdTransitionEvent_series_ne_top
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (source : CorrectedProductSourceThetaSeriesData data)
    (t : DominoTiling) (gaps : GapTriple)
    (hproper₁ : gaps.1.1 ∈ properGapMesh)
    (hproper₂ : gaps.1.2 ∈ properGapMesh)
    (hproper₃ : gaps.2 ∈ properGapMesh) :
    ∑' m, simpleRandomWalk
      (filteredThirdTransitionEvent (firstRawStagedCandidate data)
        (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
          t m gaps) ≠ ∞ := by
  let q : ℕ → ℝ≥0∞ := UpperCanonical.hlozTransitionCost 1
  let payment₁ : ℕ → ℝ≥0∞ := fun m ↦ simpleRandomWalk
    (rawOrientedSourceThetaTotalPaymentAtRank data t 1 m)
  let payment₂ : ℕ → ℝ≥0∞ := fun m ↦ simpleRandomWalk
    (rawOrientedSourceThetaTotalPaymentAtRank data t 2 m)
  let payment₃ : ℕ → ℝ≥0∞ := fun m ↦ simpleRandomWalk
    (rawOrientedSourceThetaTotalPaymentAtRank data t 3 m)
  let candidate₁ : ℕ → ℝ≥0∞ := fun m ↦
    simpleRandomWalk (firstRawStagedCandidate data t m gaps)
  let candidate₂ : ℕ → ℝ≥0∞ := fun m ↦
    simpleRandomWalk (secondRawStagedCandidate data t m gaps)
  let major : ℕ → ℝ≥0∞ := fun m ↦
    q m ^ 3 + (payment₁ m + candidate₁ m) +
      (payment₂ m + candidate₁ m + candidate₂ m) + payment₃ m
  have hq : ∑' m, q m ^ 3 ≠ ∞ := by
    simpa only [q, UpperCanonical.hlozTransitionCost_cube, one_pow,
      ENNReal.coe_one, one_mul] using
        (UpperAssembly.tsum_pSeriesWeight_ne_top
          hloz_parameter_inequalities.2.2.2.2.2.2.2.1)
  have hp₁ : ∑' m, payment₁ m ≠ ∞ :=
    simpleRandomWalk_rawOrientedSourceThetaTotalPaymentAtRank_series_ne_top
      hmax data t 1 (by omega)
  have hp₂ : ∑' m, payment₂ m ≠ ∞ :=
    simpleRandomWalk_rawOrientedSourceThetaTotalPaymentAtRank_series_ne_top
      hmax data t 2 (by omega)
  have hp₃ : ∑' m, payment₃ m ≠ ∞ :=
    simpleRandomWalk_rawOrientedSourceThetaTotalPaymentAtRank_series_ne_top
      hmax data t 3 (by omega)
  have hc₁ : ∑' m, candidate₁ m ≠ ∞ := by
    exact ne_top_of_le_ne_top (source.firstMajorant_series hmax t) <|
      ENNReal.tsum_le_tsum fun m ↦ measure_mono
        (source.firstRawStagedCandidate_subset_majorant t m gaps)
  have hc₂ : ∑' m, candidate₂ m ≠ ∞ := by
    exact ne_top_of_le_ne_top (source.secondMajorant_series hmax t) <|
      ENNReal.tsum_le_tsum fun m ↦ measure_mono
        (source.secondRawStagedCandidate_subset_majorant t m gaps)
  have hmajor : ∑' m, major m ≠ ∞ := by
    exact tsum_add_ne_top
      (tsum_add_ne_top
        (tsum_add_ne_top hq (tsum_add_ne_top hp₁ hc₁))
        (tsum_add_ne_top (tsum_add_ne_top hp₂ hc₁) hc₂)) hp₃
  have htail : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (filteredThirdTransitionEvent (firstRawStagedCandidate data)
            (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
              t m gaps) ≤ major m := by
    filter_upwards
        [eventually_tilingEndpointSourceRowParametersAt,
          eventually_initialBudget48_mul_prop49CandidateRatioEnvelope_mul_meshEscapeCost_le
            (6 * prop49WindowRatioConstant)
              (mul_nonneg (by norm_num) prop49WindowRatioConstant_pos.le) gaps.1.1,
          eventually_initialBudget48_mul_prop49CandidateRatioEnvelope_mul_meshEscapeCost_le
            (6 * prop49WindowRatioConstant)
              (mul_nonneg (by norm_num) prop49WindowRatioConstant_pos.le) gaps.1.2,
          eventually_initialBudget48_mul_prop49CandidateRatioEnvelope_mul_meshEscapeCost_le
            (6 * prop49WindowRatioConstant)
              (mul_nonneg (by norm_num) prop49WindowRatioConstant_pos.le) gaps.2,
          eventually_ofReal_literalEscapeProbability_le_hlozTransitionCost_of_one_le
            1 (by norm_num)] with m hparameters hnumeric₁ hnumeric₂ hnumeric₃ hcost
    exact measure_filteredThird_le_cubic_add_payments_candidates data t m gaps 0
      hproper₁ hproper₂ hproper₃ hparameters.m_gt_one hparameters.window
      hparameters.shell_arithmetic hparameters.width
        hparameters.external_arithmetic
      (fun _ ↦ hnumeric₁) (fun _ ↦ hnumeric₂) (fun _ ↦ hnumeric₃)
      hcost
  exact tsum_ne_top_of_eventually_le
    (fun m ↦ measure_ne_top simpleRandomWalk _) hmajor htail

theorem filteredThird_meshBranchUnion_series_ne_top
    (mesh : Finset GapScale)
    (hmesh : ∀ a ∈ mesh, a ∈ properGapMesh)
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (source : CorrectedProductSourceThetaSeriesData data)
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (UpperAssembly.meshBranchUnion mesh
        (filteredThirdTransitionEvent (firstRawStagedCandidate data)
          (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
            t m)) ≠ ∞ := by
  apply meshBranchUnion_series_ne_top_of_branch mesh
  intro gaps hgaps
  obtain ⟨hproper₁, hproper₂, hproper₃⟩ :=
    HLOZNoLazyInitialBudgetMixedTransitionFactors.mem_meshTriples_components
      (mesh := mesh) hgaps
  apply filteredThirdTransitionEvent_series_ne_top
    (hmax := hmax) (data := data) (source := source) (t := t)
    (gaps := gaps)
  · exact hmesh _ hproper₁
  · exact hmesh _ hproper₂
  · exact hmesh _ hproper₃

theorem candidatePaid_meshBranchUnion_series_ne_top
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (source : CorrectedProductSourceThetaSeriesData data)
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (UpperAssembly.meshBranchUnion properGapMesh
        (candidatePaidBadHistoryEvent (firstRawStagedCandidate data)
          (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
            t m)) ≠ ∞ := by
  apply candidatePaidBadHistoryEvent_series_ne_top_of_rank_majorants
    properGapMesh (firstRawStagedCandidate data)
      (secondRawStagedCandidate data) (thirdRawStagedCandidate data)
    (fun t m ↦ rawRankRecurrencePaymentEvent data t 1 m ∪
      (source.balance t m ∪ source.sourceOne t m))
    (fun t m ↦ rawRankRecurrencePaymentEvent data t 2 m ∪
      (source.balance t m ∪ source.sourceTwo t m))
    (fun t m ↦ rawRankRecurrencePaymentEvent data t 3 m ∪
      (source.balance t m ∪ source.sourceThree t m)) t
  · intro m gaps _
    exact source.firstRawStagedCandidate_subset_majorant t m gaps
  · intro m gaps _
    exact source.secondRawStagedCandidate_subset_majorant t m gaps
  · intro m gaps _
    exact source.thirdRawStagedCandidate_subset_majorant t m gaps
  · exact source.firstMajorant_series hmax t
  · exact source.secondMajorant_series hmax t
  · exact source.thirdMajorant_series hmax t

theorem hlozExceptional_series_ne_top
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (source : CorrectedProductSourceThetaSeriesData data)
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk (hlozExceptionalEvent t m) ≠ ∞ :=
  simpleRandomWalk_hlozExceptional_series_ne_top_of_balance_rank_source_series
    hmax data t (source.candidateLocalBalance_series t)
      (source.candidateLocalOne_series t) (source.candidateLocalTwo_series t)
      (source.candidateLocalThree_series t) (source.complement_series t)

theorem hlozSeparatedLevelEvent_series_ne_top
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (source : CorrectedProductSourceThetaSeriesData data)
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk (hlozSeparatedLevelEvent t m) ≠ ∞ := by
  let paid : BranchEvent := candidatePaidBadHistoryEvent
    (firstRawStagedCandidate data) (secondRawStagedCandidate data)
      (thirdRawStagedCandidate data)
  have hexception : ∑' m, simpleRandomWalk
      (sourceCorrectFilteredExceptionalEvent paid t m) ≠ ∞ :=
    sourceCorrectFilteredExceptional_series_ne_top paid t
      (hlozExceptional_series_ne_top hmax data source t)
      (candidatePaid_meshBranchUnion_series_ne_top hmax data source t)
  have hterminal :=
    filteredThird_meshBranchUnion_series_ne_top properGapMesh
      (fun _ ha ↦ ha) hmax data source t
  have hunion := measure_union_series_ne_top hexception hterminal
  exact ne_top_of_le_ne_top hunion <| ENNReal.tsum_le_tsum fun m ↦
    measure_mono <| by
      simpa only [paid, filteredThirdTransitionEvent] using
        (hlozSeparatedLevelEvent_sourceCorrect_filtered_mesh_cover
          (firstFactorBadHistory (firstRawStagedCandidate data))
          (secondFactorBadHistory (secondRawStagedCandidate data))
          (thirdFactorBadHistory (thirdRawStagedCandidate data)) paid
          (noLazy_terminalFilteredBadHistoryRouting
            (firstRawStagedCandidate data) (secondRawStagedCandidate data)
              (thirdRawStagedCandidate data)) t m)

/-- The completed structural-past recurrence supplies the upper half of the
HLOZ conclusion from the corrected source product and its concrete summable
source data. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk)
    (data : FullBetaSourceCorrectAllTilingProductData)
    (source : CorrectedProductSourceThetaSeriesData data) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 := by
  have hscreened : ∀ t : DominoTiling,
      ∑' m, simpleRandomWalk (hlozSeparatedLevelEvent t m) ≠ ∞ :=
    fun t ↦ hlozSeparatedLevelEvent_series_ne_top hmax data source t
  have hsum : ∑' m, simpleRandomWalk (levelFavoriteSet m 4) ≠ ∞ :=
    level_event_summable_of_six_tilings simpleRandomWalk
      levelFavoriteSet_four_subset_six_hloz_tilings hscreened
  exact UpperAssembly.ae_eventually_favoriteCount_le_three_of_M4_summable
    simpleRandomWalk hsum simpleRandomWalk_maxLocalTime_tendsto

/-- The concrete source product and balance-series adapter discharge all
inputs to the upper half of the HLOZ conclusion. -/
theorem simpleRandomWalk_ae_eventually_favoriteCount_le_three_of_lowerDeviation
    (hmax : HasPlanarMaximumLowerDeviation simpleRandomWalk) :
    ∀ᵐ s ∂simpleRandomWalk, ∀ᶠ n in atTop, favoriteCount s n ≤ 3 :=
  simpleRandomWalk_ae_eventually_favoriteCount_le_three hmax
    HLOZConcreteFullBetaProductData.concreteFullBetaProductData
    (correctedProductSourceThetaSeriesData_of_balance hmax
      concretePositiveInterfaceBalanceSeriesData)

end

end Erdos1165.HLOZStructuralPastAdditiveRecurrence
